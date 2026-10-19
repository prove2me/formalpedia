-- Prove2me | Theorems.Thm_TypeDensity_coordinate_transition_ideal_identity
-- name    : TypeDensity.coordinate_transition_ideal_identity
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:34:06.508271+00:00
-- url     : https://prove2.me/theorems/60465bbe-65a4-4af0-8f12-97e6c2f3ddb6
-- title:
--   The transition map between two division charts of the same cell intertwines their coordinate-ideal maps.
-- statement:
--   The transition map between two division charts of the same cell intertwines their coordinate-ideal maps.
-- source:
--   TypeDensity/Measure/Atlas.lean#L141-L159

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_principal_ideal_unit_invariance
import Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
import Theorems.Thm_TypeDensity_normalizing_factor_is_unit
import Theorems.Thm_TypeDensity_normalizer_generator_equation
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.coordinate_transition_ideal_identity (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsLocalRing R]
    (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (f g : R) (c : Fin n → R)
    (F : R ≃ₗ[O] ((Fin n → O) × R)) (hF : ∀ s, F.symm s = divisionMap g c s) (h0 : R)
    (hfg : f = g + pi • h0) (z : Fin n → O) :
    coordinateIdeal pi g c (idealTransition pi b c F h0 z) = coordinateIdeal pi f b z := by sorry
