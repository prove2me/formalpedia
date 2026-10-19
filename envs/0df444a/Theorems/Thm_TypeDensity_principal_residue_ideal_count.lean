-- Prove2me | Theorems.Thm_TypeDensity_principal_residue_ideal_count
-- name    : TypeDensity.principal_residue_ideal_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:10.885731+00:00
-- url     : https://prove2.me/theorems/484a0a63-1f61-4070-897e-8caa9e37eeab
-- title:
--   Count of the principal ideals `(f)` of the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` whose generator satisfies a unit-invariant condition `P` of colength `N` that, read on the truncation `k⟦T, X⟧ ⧸ truncIde
-- statement:
--   This counts the principal ideals `(f)` of the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` whose generator satisfies a unit-invariant condition `P` of colength `N` that, read on the truncation `k⟦T, X⟧ ⧸ truncIdeal k a b (N + 1)`, says: the coefficients on `A` vanish and those on `B` do not. With `q = #k`, the count times `(q - 1) q^(#A + #B - 1)` is `(q - 1)^#B q^N`.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L448-L554

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_coordinate_constraint_count
import Theorems.Thm_TypeDensity_maximal_ideal_power_kills
import Theorems.Thm_TypeDensity_principal_generator_orbit_count
import Theorems.Thm_TypeDensity_truncCoeffs_apply
import Theorems.Thm_TypeDensity_isUnit_mk_truncIdeal_iff
import Theorems.Thm_TypeDensity_card_mul_eq_zero_eq_card_quotient
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.principal_residue_ideal_count (k : Type) [Field k] [Finite k] (a b N : ℕ) (ha : 0 < a)
    (P : TwoSeries k → Prop) (Q : SpecialFiber k a b → Prop)
    (hQ : ∀ F, Q (Ideal.Quotient.mk _ F) ↔ P F) (hunit : ∀ U F, IsUnit U → P F → P (U * F))
    (hlen : ∀ F, P F → Module.length (TwoSeries k)
      (TwoSeries k ⧸ (monomialIdeal k a b ⊔ Ideal.span {F})) = N)
    (hcard : ∀ F, P F →
      Nat.card (TwoSeries k ⧸ (monomialIdeal k a b ⊔ Ideal.span {F})) = Nat.card k ^ N)
    (A B : Finset (truncIndex a b (N + 1))) (hAB : Disjoint A B) (hB : B.Nonempty)
    (hcrit : ∀ F, P F ↔ (∀ s ∈ A, truncCoeffs k a b (N + 1) F s = 0) ∧
      ∀ s ∈ B, truncCoeffs k a b (N + 1) F s ≠ 0) :
    Nat.card {I : Ideal (SpecialFiber k a b) // ∃ f, I = Ideal.span {f} ∧ Q f} *
        ((Nat.card k - 1) * Nat.card k ^ (A.card + B.card - 1)) =
      (Nat.card k - 1) ^ B.card * Nat.card k ^ N := by sorry
