/-
Copyright (c) 2026 Aviv Barnatan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Barnatan
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# The apolarity lemma

The polynomial ring `MvPolynomial σ R` acts on itself by differentiation, with `X i`
acting as `∂/∂xᵢ`. The apolar ideal of a polynomial `F` is the annihilator of `F` under
this action.

The apolarity lemma states that a form of degree `d` lies in the span of the `d`-th
powers of the linear forms dual to the points of a set `P` in projective space if and
only if the homogeneous ideal of `P` is contained in the apolar ideal of `F`.

## Main definitions

* `MvPolynomial.apolarHom`: the action by differentiation, as an algebra homomorphism
  into `Module.End R (MvPolynomial σ R)`.
* `MvPolynomial.apolarIdeal`: the apolar ideal `F^⊥`.

## Main results

* `MvPolynomial.IsHomogeneous.mem_span_pow_iff`: the apolarity lemma.
* `MvPolynomial.apolarHom_monomial_monomial`: the action on monomials, in closed form.
* `MvPolynomial.IsHomogeneous.apolarHom_linear_pow`: the action of a homogeneous operator
  on a power of a linear form.
* `MvPolynomial.IsHomogeneous.eval_smul`, `MvPolynomial.pderiv_comm`: general-purpose
  lemmas that could move next to `IsHomogeneous` and `pderiv` respectively.

## References

* A. Iarrobino, V. Kanev, *Power sums, Gorenstein algebras, and determinantal loci*,
  Lemma 1.15.
-/

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- Partial derivatives commute. -/
theorem pderiv_comm (i j : σ) (f : MvPolynomial σ R) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · simp only [pderiv_monomial, Finsupp.tsub_apply, Finsupp.single_apply,
        if_neg hij, if_neg (Ne.symm hij), tsub_zero]
      rw [tsub_right_comm, mul_right_comm]
  | add p q hp hq => simp only [map_add, hp, hq]

open scoped IsMulCommutative in
/-- The action of `MvPolynomial σ R` on itself by differentiation: the algebra
homomorphism sending `X i` to `∂/∂xᵢ`. -/
noncomputable def apolarHom : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  let A := Algebra.adjoin R
    (Set.range fun i => ((pderiv i).toLinearMap : Module.End R (MvPolynomial σ R)))
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin R <| by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact LinearMap.ext (pderiv_comm i j)
  A.val.comp <| aeval fun i =>
    (⟨(pderiv i).toLinearMap, Algebra.subset_adjoin (Set.mem_range_self i)⟩ : A)

/-- The apolar ideal of `F`: the polynomial differential operators annihilating `F`. -/
noncomputable def apolarIdeal (F : MvPolynomial σ R) : Ideal (MvPolynomial σ R) where
  carrier := {g | apolarHom g F = 0}
  zero_mem' := by simp
  add_mem' {g h} hg hh := by
    change apolarHom (g + h) F = 0
    rw [map_add, LinearMap.add_apply, hg, hh, add_zero]
  smul_mem' c g hg := by
    change apolarHom (c * g) F = 0
    rw [map_mul, Module.End.mul_apply, show apolarHom g F = 0 from hg, map_zero]

/-! ### Action on monomials -/

/-- `X i` acts as `∂/∂xᵢ`. -/
@[simp]
theorem apolarHom_X (i : σ) :
    apolarHom (X i : MvPolynomial σ R) = (pderiv i).toLinearMap := by
  simp [apolarHom, aeval_X]

/-- Constants act by scalar multiplication. -/
theorem apolarHom_C_apply (a : R) (F : MvPolynomial σ R) :
    apolarHom (C a) F = a • F := by
  rw [← algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The iterated partial derivative of a monomial, via descending factorials.
The formula needs no side condition: if `n > α i` both sides vanish. -/
theorem pderiv_pow_monomial (i : σ) (n : ℕ) (α : σ →₀ ℕ) (a : R) :
    ((pderiv i).toLinearMap ^ n) (monomial α a) =
      monomial (α - Finsupp.single i n) ((α i).descFactorial n • a) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [Derivation.coeFn_coe, pderiv_monomial]
    rw [tsub_tsub, ← Finsupp.single_add, Finsupp.tsub_apply, Finsupp.single_eq_same]
    congr 1
    simp only [Nat.descFactorial_succ, nsmul_eq_mul, Nat.cast_mul]
    ring

/-- The apolarity action on monomials, in closed form. The formula needs no side
condition: if `β ≰ α` some descending factorial vanishes and both sides are zero. -/
theorem apolarHom_monomial_monomial (β α : σ →₀ ℕ) (b a : R) :
    apolarHom (monomial β b) (monomial α a) =
      monomial (α - β) ((∏ j ∈ β.support, (α j).descFactorial (β j)) • (b * a)) := by
  classical
  induction β using Finsupp.induction with
  | zero => simp [smul_monomial]
  | single_add i n β hi hn ih =>
    have hβi : β i = 0 := Finsupp.notMem_support_iff.mp hi
    have hss : (Finsupp.single i n).support = {i} := by simp [Finsupp.support_single, hn]
    have hdisj : Disjoint (Finsupp.single i n).support β.support := by
      rw [hss]; exact Finset.disjoint_singleton_left.mpr hi
    rw [show monomial (Finsupp.single i n + β) b
          = monomial (Finsupp.single i n) 1 * monomial β b by rw [monomial_mul, one_mul],
      map_mul, Module.End.mul_apply, ih, ← X_pow_eq_monomial, map_pow, apolarHom_X,
      pderiv_pow_monomial, tsub_tsub, add_comm β (Finsupp.single i n)]
    congr 1
    rw [Finsupp.tsub_apply, hβi, tsub_zero, smul_smul]
    congr 1
    rw [Finsupp.support_add_eq hdisj, hss,
      Finset.prod_union (Finset.disjoint_singleton_left.mpr hi),
      Finset.prod_singleton, Finsupp.add_apply, Finsupp.single_eq_same, hβi, add_zero]
    exact congrArg _ (Finset.prod_congr rfl fun j hj => by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by rintro rfl; exact hi hj), zero_add])

/-! ### Action on powers of linear forms -/

private theorem descFactorial_add (d e n : ℕ) :
    d.descFactorial (e + n) = d.descFactorial e * (d - e).descFactorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ,
      tsub_add_eq_tsub_tsub]
    ring

/-- The derivative of a linear form is its coefficient. -/
theorem pderiv_linear [Fintype σ] (i : σ) (c : σ → R) :
    pderiv i (∑ j, c j • X j : MvPolynomial σ R) = C (c i) := by
  classical
  rw [map_sum, Finset.sum_eq_single i
    (fun j _ hj => by rw [Derivation.map_smul, pderiv_X_of_ne hj, smul_zero])
    (fun h => absurd (Finset.mem_univ i) h),
    Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]

/-- Iterated derivatives of powers of a linear form. -/
theorem pderiv_pow_linear_pow [Fintype σ] (i : σ) (c : σ → R) (n d : ℕ) :
    ((pderiv i).toLinearMap ^ n) ((∑ j, c j • X j : MvPolynomial σ R) ^ d) =
      d.descFactorial n • c i ^ n • (∑ j, c j • X j) ^ (d - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_nsmul, map_smul]
    simp only [Derivation.coeFn_coe]
    rw [pderiv_pow, pderiv_linear, tsub_tsub]
    simp only [nsmul_eq_mul, smul_eq_C_mul, Nat.descFactorial_succ, pow_succ, Nat.cast_mul,
      C_mul]
    ring

/-- The action of a monomial operator on a power of a linear form. -/
theorem apolarHom_monomial_linear_pow [Fintype σ] (β : σ →₀ ℕ) (b : R) (c : σ → R)
    (d : ℕ) :
    apolarHom (monomial β b) ((∑ j, c j • X j : MvPolynomial σ R) ^ d) =
      d.descFactorial (Finsupp.degree β) •
        (β.prod fun j m => c j ^ m) • b •
          (∑ j, c j • X j) ^ (d - Finsupp.degree β) := by
  classical
  induction β using Finsupp.induction with
  | zero => simp
  | single_add i n β hi hn ih =>
    rw [show monomial (Finsupp.single i n + β) b
          = monomial (Finsupp.single i n) 1 * monomial β b by rw [monomial_mul, one_mul],
      map_mul, Module.End.mul_apply, ih, map_nsmul, map_smul, map_smul,
      ← X_pow_eq_monomial, map_pow apolarHom (X i) n, apolarHom_X, pderiv_pow_linear_pow,
      map_add Finsupp.degree, Finsupp.degree_single,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun j m₁ m₂ => pow_add _ _ _),
      add_comm n (Finsupp.degree β), descFactorial_add, tsub_add_eq_tsub_tsub]
    simp only [Finsupp.prod_single_index, pow_zero]
    simp only [nsmul_eq_mul, smul_eq_C_mul, Nat.cast_mul, map_mul]
    ring

/-- A homogeneous operator `g` of degree `e` sends `ℓ^d` to a multiple of `ℓ^(d - e)`,
scaled by the value of `g` at the coefficient vector of `ℓ`. -/
theorem IsHomogeneous.apolarHom_linear_pow [Fintype σ] {g : MvPolynomial σ R} {e : ℕ}
    (hg : g.IsHomogeneous e) (c : σ → R) (d : ℕ) :
    apolarHom g ((∑ j, c j • X j : MvPolynomial σ R) ^ d) =
      d.descFactorial e • eval c g • (∑ j, c j • X j) ^ (d - e) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, LinearMap.sum_apply, map_sum, Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : Finsupp.degree α = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hg (mem_support_iff.mp hα)
  rw [apolarHom_monomial_linear_pow, hdeg, eval_monomial]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_mul]
  ring

/-! ### Homogeneous components and cones -/

/-- A homogeneous polynomial scales by `t ^ n` under `v ↦ t • v`. -/
theorem IsHomogeneous.eval_smul {g : MvPolynomial σ R} {n : ℕ}
    (hg : g.IsHomogeneous n) (t : R) (v : σ → R) :
    eval (t • v) g = t ^ n * eval v g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : Finsupp.degree α = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hg (mem_support_iff.mp hα)
  rw [eval_monomial, eval_monomial, ← hdeg, Finsupp.degree_apply]
  change coeff α g * ∏ j ∈ α.support, (t • v) j ^ α j
      = t ^ (∑ j ∈ α.support, α j) * (coeff α g * ∏ j ∈ α.support, v j ^ α j)
  rw [Finset.prod_congr rfl fun j _ => show ((t • v) j) ^ α j = t ^ α j * v j ^ α j by
      rw [Pi.smul_apply, smul_eq_mul, mul_pow],
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

variable {k : Type*} [Field k] [CharZero k] [Fintype σ]

omit [Fintype σ] in
/-- If a polynomial vanishes on the whole line through `v`, so does each of its
homogeneous components. -/
theorem eval_homogeneousComponent_eq_zero_of_forall_smul {g : MvPolynomial σ k} {v : σ → k}
    (hv : ∀ t : k, eval (t • v) g = 0) (n : ℕ) :
    eval v (homogeneousComponent n g) = 0 := by
  by_cases hn : g.totalDegree < n
  · rw [homogeneousComponent_eq_zero _ _ hn, map_zero]
  · set q : Polynomial k :=
      ∑ m ∈ Finset.range (g.totalDegree + 1),
        Polynomial.C (eval v (homogeneousComponent m g)) * Polynomial.X ^ m with hq
    have hqeval : ∀ t : k, q.eval t = 0 := fun t => by
      have h0 := hv t
      conv_lhs at h0 => rw [← sum_homogeneousComponent g]
      rw [map_sum] at h0
      rw [hq, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← h0]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [(homogeneousComponent_isHomogeneous m g).eval_smul t v]
      ring
    haveI : Infinite k := Infinite.of_injective _ Nat.cast_injective
    have hq0 : q = 0 := Polynomial.zero_of_eval_zero q hqeval
    have hcoeff := congrArg (fun p => Polynomial.coeff p n) hq0
    simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq] at hcoeff
    rwa [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp hn)))] at hcoeff

omit [CharZero k] [Fintype σ] in
private theorem aeval_self_eq_eval (v : σ → k) (p : MvPolynomial σ k) :
    aeval v p = eval v p := by
  rw [aeval_def, Algebra.algebraMap_self]
  rfl

omit [CharZero k] [Fintype σ] in
private theorem eq_of_le_of_degree_eq {β γ : σ →₀ ℕ} (hle : β ≤ γ)
    (hdeg : Finsupp.degree β = Finsupp.degree γ) : β = γ := by
  have h := tsub_add_cancel_of_le hle
  have hd := congrArg Finsupp.degree h
  rw [map_add, hdeg] at hd
  have h0 : Finsupp.degree (γ - β) = 0 := by omega
  rw [(Finsupp.degree_eq_zero_iff _).mp h0, zero_add] at h
  exact h

omit [CharZero k] in
private theorem monomial_symm_eq_prod (α : σ → ℕ) :
    monomial (Finsupp.equivFunOnFinite.symm α) (1 : k) = ∏ x, (X x : MvPolynomial σ k) ^ α x :=
  calc monomial (Finsupp.equivFunOnFinite.symm α) (1 : k)
      = ∏ x ∈ (Finsupp.equivFunOnFinite.symm α).support,
          X x ^ (Finsupp.equivFunOnFinite.symm α) x := prod_X_pow_eq_monomial.symm
    _ = ∏ x, X x ^ (Finsupp.equivFunOnFinite.symm α) x :=
        Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by
          rw [Finsupp.notMem_support_iff.mp hx, pow_zero]
    _ = ∏ x, X x ^ α x := by simp

omit [CharZero k] in
private theorem linear_pow_eq_sum [DecidableEq σ] (c : σ → k) (d : ℕ) :
    (∑ i, c i • X i : MvPolynomial σ k) ^ d =
      ∑ α ∈ Finset.univ.piAntidiag d,
        ((Nat.multinomial Finset.univ α : k) * ∏ i, c i ^ α i) •
          monomial (Finsupp.equivFunOnFinite.symm α) 1 := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [monomial_symm_eq_prod]
  simp only [smul_eq_C_mul, mul_pow, map_mul, map_natCast, map_prod, map_pow]
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- The key diagonal computation for the backward direction: the operator dual to `φ`
built from degree-`d` monomials pairs with a degree-`d` monomial to
`(c * φ (monomial γ 1)) • 1`. -/
private theorem apolarHom_dual_sum_monomial [DecidableEq σ]
    (φ : Module.Dual k (MvPolynomial σ k)) {d : ℕ} {γ : σ →₀ ℕ}
    (hγd : Finsupp.degree γ = d) (c : k) :
    apolarHom (∑ α ∈ Finset.univ.piAntidiag d,
        ((∏ i, (α i).factorial : ℕ) : k)⁻¹ •
          φ (monomial (Finsupp.equivFunOnFinite.symm α) 1) •
            monomial (Finsupp.equivFunOnFinite.symm α) 1) (monomial γ c)
      = (c * φ (monomial γ 1)) • 1 := by
  rw [map_sum, LinearMap.sum_apply,
    Finset.sum_eq_single (Finsupp.equivFunOnFinite γ)
      (fun b hb hbne => ?_) (fun hnot => ?_)]
  · -- the diagonal term
    rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
      Equiv.symm_apply_apply, apolarHom_monomial_monomial, tsub_self]
    simp only [Nat.descFactorial_self, one_mul]
    have hprod : (∏ i, (γ i).factorial : ℕ) = ∏ j ∈ γ.support, (γ j).factorial :=
      (Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by
        rw [Finsupp.notMem_support_iff.mp hx]; rfl).symm
    have hfac : ((∏ i, (γ i).factorial : ℕ) : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (γ i).factorial_ne_zero)
    rw [show ∀ x : k, (monomial (0 : σ →₀ ℕ)) x = x • (1 : MvPolynomial σ k) from
        fun x => by rw [← C_apply, smul_eq_C_mul, mul_one],
      ← hprod, smul_smul, smul_smul]
    congr 1
    rw [show (∏ i, (Finsupp.equivFunOnFinite γ i).factorial) = ∏ i, (γ i).factorial from rfl,
      nsmul_eq_mul]
    field_simp
  · -- off-diagonal terms vanish
    obtain ⟨hbsum, -⟩ := Finset.mem_piAntidiag.mp hb
    have hdegb : Finsupp.degree (Finsupp.equivFunOnFinite.symm b) = Finsupp.degree γ := by
      rw [hγd, Finsupp.degree_eq_sum]
      simpa using hbsum
    have hne : Finsupp.equivFunOnFinite.symm b ≠ γ := fun h =>
      hbne (by rw [← h, Equiv.apply_symm_apply])
    obtain ⟨i, hi⟩ : ∃ i, γ i < (Finsupp.equivFunOnFinite.symm b) i := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hne (eq_of_le_of_degree_eq ((Finsupp.le_iff _ _).mpr fun i _ => hcon i) hdegb)
    have hzero : (∏ j ∈ (Finsupp.equivFunOnFinite.symm b).support,
        (γ j).descFactorial ((Finsupp.equivFunOnFinite.symm b) j)) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.descFactorial_eq_zero_iff_lt.mpr hi)
    rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
      apolarHom_monomial_monomial, hzero]
    simp
  · -- the diagonal index is a member
    refine absurd (Finset.mem_piAntidiag.mpr ⟨?_, fun i _ => Finset.mem_univ i⟩) hnot
    change ∑ i, γ i = d
    rw [← Finsupp.degree_eq_sum]
    exact hγd

/-- **The apolarity lemma**: a form `F` of degree `d` lies in the span of the `d`-th
powers of the linear forms dual to the points of `P` if and only if the homogeneous
ideal of `P`, that is, the vanishing ideal of its affine cone, is contained in the
apolar ideal of `F`. -/
theorem IsHomogeneous.mem_span_pow_iff {d : ℕ} {F : MvPolynomial σ k}
    (hF : F.IsHomogeneous d) (P : Set (Projectivization k (σ → k))) :
    F ∈ Submodule.span k ((fun x => (∑ i, x.rep i • X i) ^ d) '' P) ↔
      vanishingIdeal k (⋃ x ∈ P, (x.submodule : Set (σ → k))) ≤ apolarIdeal F := by
  constructor
  · intro hFspan g hg
    change apolarHom g F = 0
    clear hF
    have hgv : ∀ x ∈ P, ∀ t : k, eval (t • x.rep) g = 0 := by
      intro x hx t
      have hmem : t • x.rep ∈ ⋃ y ∈ P, (y.submodule : Set (σ → k)) :=
        Set.mem_biUnion hx (by
          rw [SetLike.mem_coe, Projectivization.submodule_eq]
          exact Submodule.mem_span_singleton.mpr ⟨t, rfl⟩)
      have h0 := mem_vanishingIdeal_iff.mp hg _ hmem
      rwa [aeval_self_eq_eval] at h0
    induction hFspan using Submodule.span_induction with
    | mem F' hF' =>
      obtain ⟨x, hx, rfl⟩ := hF'
      conv_lhs => rw [← sum_homogeneousComponent g]
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [(homogeneousComponent_isHomogeneous n g).apolarHom_linear_pow,
        eval_homogeneousComponent_eq_zero_of_forall_smul (hgv x hx) n, zero_smul, smul_zero]
    | zero => exact map_zero _
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | smul r u _ hu => rw [map_smul, hu, smul_zero]
  · intro hle
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    classical
    have hφgen : ∀ x ∈ P, φ ((∑ i, x.rep i • X i) ^ d) = 0 := fun x hx =>
      (Submodule.mem_dualAnnihilator φ).mp hφ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    set gφ : MvPolynomial σ k :=
      ∑ α ∈ Finset.univ.piAntidiag d,
        ((∏ i, (α i).factorial : ℕ) : k)⁻¹ •
          φ (monomial (Finsupp.equivFunOnFinite.symm α) 1) •
            monomial (Finsupp.equivFunOnFinite.symm α) 1 with hgφdef
    have hdeg_symm : ∀ α ∈ (Finset.univ.piAntidiag d : Finset (σ → ℕ)),
        Finsupp.degree (Finsupp.equivFunOnFinite.symm α) = d := fun α hα => by
      obtain ⟨hsum, -⟩ := Finset.mem_piAntidiag.mp hα
      rw [Finsupp.degree_eq_sum]
      simpa [Finsupp.coe_equivFunOnFinite_symm] using hsum
    have hgφ_hom : gφ.IsHomogeneous d := by
      rw [hgφdef, ← mem_homogeneousSubmodule]
      refine Submodule.sum_mem _ fun α hα =>
        Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
      rw [mem_homogeneousSubmodule]
      exact isHomogeneous_monomial _ (hdeg_symm α hα)
    have hgφ_eval : ∀ x ∈ P, eval x.rep gφ = 0 := by
      intro x hx
      have hkey : (d.factorial : k) * eval x.rep gφ = φ ((∑ i, x.rep i • X i) ^ d) := by
        conv_rhs => rw [linear_pow_eq_sum]
        rw [map_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun α hα => ?_
        obtain ⟨hsum, -⟩ := Finset.mem_piAntidiag.mp hα
        have hspec : ((∏ i, (α i).factorial : ℕ) : k) * (Nat.multinomial Finset.univ α : k)
            = (d.factorial : k) := by
          rw [← Nat.cast_mul, Nat.multinomial_spec, hsum]
        have hfac : ((∏ i, (α i).factorial : ℕ) : k) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (α i).factorial_ne_zero)
        have hevalmono : eval x.rep (monomial (Finsupp.equivFunOnFinite.symm α) (1 : k))
            = ∏ i, x.rep i ^ α i := by
          rw [monomial_symm_eq_prod, map_prod]
          simp
        rw [smul_eval, smul_eval, hevalmono, map_smul, smul_eq_mul, ← hspec]
        field_simp
      have h0 := hφgen x hx
      rw [← hkey] at h0
      exact (mul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr d.factorial_ne_zero)
    have hgφ_mem : gφ ∈ vanishingIdeal k (⋃ x ∈ P, (x.submodule : Set (σ → k))) := by
      rw [mem_vanishingIdeal_iff]
      rintro v hv
      rw [aeval_self_eq_eval]
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hv
      obtain ⟨x, hx, hvmem⟩ := hv
      rw [Projectivization.submodule_eq, Submodule.mem_span_singleton] at hvmem
      obtain ⟨t, rfl⟩ := hvmem
      rw [hgφ_hom.eval_smul, hgφ_eval x hx, mul_zero]
    have happ : apolarHom gφ F = 0 := hle hgφ_mem
    have hdiag : apolarHom gφ F = φ F • 1 := by
      rw [hgφdef]
      conv_lhs => rw [F.as_sum]
      rw [map_sum,
        Finset.sum_congr rfl fun γ hγ => apolarHom_dual_sum_monomial φ
          (by rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.mp hγ)) (coeff γ F),
        ← Finset.sum_smul]
      congr 1
      conv_rhs => rw [F.as_sum, map_sum]
      exact Finset.sum_congr rfl fun γ hγ => by
        rw [show (monomial γ) (coeff γ F) = coeff γ F • monomial γ 1 by
          rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rw [happ] at hdiag
    have h1 : φ F • (1 : MvPolynomial σ k) = 0 := hdiag.symm
    rw [smul_eq_C_mul, mul_one] at h1
    exact (C_injective σ k) (by rw [map_zero]; exact h1)

end MvPolynomial
