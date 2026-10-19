-- Prove2me | Theorems.Thm_TypeDensity_frobenius_fraction_extension
-- name    : TypeDensity.frobenius_fraction_extension
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:07.966156+00:00
-- url     : https://prove2.me/theorems/c7b02226-8a24-4e38-8f87-66e0ed73acd6
-- title:
--   The Frobenius iterates of `Oδ = O[X]/(Φ)` extend to automorphisms `τ i` of `Kδ = Frac Oδ` fixing `K`;
-- statement:
--   The Frobenius iterates of `Oδ = O[X]/(Φ)` extend to automorphisms `τ i` of `Kδ = Frac Oδ` fixing `K`; `τ` is a group action of `ℕ` with `τ δ = id`, and the fixed field of `τ 1` is `K`.
-- source:
--   TypeDensity/Unramified/DescentTypes.lean#L123-L184

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_frobenius_fixed_ring
import Theorems.Thm_TypeDensity_frobenius_pow_degree_eq_id
import Theorems.Thm_TypeDensity_unramified_is_dvr
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open Polynomial

theorem TypeDensity.frobenius_fraction_extension (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
      algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) :
    ∃ τ : ℕ → (BaseField (AdjoinRoot Φ) ≃+* BaseField (AdjoinRoot Φ)),
      (∀ (i : ℕ) (x : AdjoinRoot Φ), τ i (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) x) =
        algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (frobeniusIter O Φ i x))
      ∧ (∀ (i : ℕ) (y : BaseField O), τ i (ι y) = ι y)
      ∧ τ 0 = RingEquiv.refl (BaseField (AdjoinRoot Φ)) ∧ (∀ i : ℕ, τ (i + 1) = (τ i).trans (τ 1))
      ∧ (∀ z : BaseField (AdjoinRoot Φ), τ Φ.natDegree z = z)
      ∧ (∀ z : BaseField (AdjoinRoot Φ), τ 1 z = z → ∃ y : BaseField O, ι y = z) := by sorry
