-- Prove2me | Theorems.Thm_TypeDensity_frobenius_fixed_ring
-- name    : TypeDensity.frobenius_fixed_ring
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:41.396209+00:00
-- url     : https://prove2.me/theorems/39a12523-0b61-4f74-bf7c-f30057bba31a
-- title:
--   The elements of `O[X]/(Φ)` fixed by the Frobenius are exactly the elements of `O`.
-- statement:
--   The elements of `O[X]/(Φ)` fixed by the Frobenius are exactly the elements of `O`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L511-L539

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_base_ideal_pure
import Theorems.Thm_TypeDensity_finite_field_frobenius_fixed_points
import Theorems.Thm_TypeDensity_unramified_adic_complete
import Theorems.Thm_TypeDensity_frobenius_residue_action
import Theorems.Thm_TypeDensity_residue_extension_field
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
open scoped BigOperators ENNReal

theorem TypeDensity.frobenius_fixed_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a : AdjoinRoot Φ)
    (ha : unramifiedFrobenius O Φ a = a) :
    ∃ c : O, algebraMap O (AdjoinRoot Φ) c = a := by sorry
