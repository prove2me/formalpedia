-- Prove2me | Theorems.Thm_TypeDensity_direction_point_overlap_maximal
-- name    : TypeDensity.direction_point_overlap_maximal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:34.535989+00:00
-- url     : https://prove2.me/theorems/2545653b-dede-4d1f-9284-67f09f28e54e
-- title:
--   For a nonzero affine direction, the direction point generates a maximal ideal of the overlap chart that contains `t` and contracts back to the direction point.
-- statement:
--   For a nonzero affine direction, the direction point generates a maximal ideal of the overlap chart that contains `t` and contracts back to the direction point.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L575-L616

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
import Theorems.Thm_TypeDensity_direction_point_maximal
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.direction_point_overlap_maximal (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (e : (BlowupChart R S.t S.x ⧸ chartExceptional R S.t S.x) ≃+* Polynomial
      (IsLocalRing.ResidueField R)) (he : ∀ r : R,
      e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartBase R S.t S.x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartSlope R S.t S.x)) = Polynomial.X)
    (φ : AffineDirection (IsLocalRing.ResidueField R))
    (hφ : φ ≠ zeroAffine (IsLocalRing.ResidueField R)) :
    ((directionPoint R S.t S.x e φ).map (algebraMap (BlowupChart R S.t S.x)
      (BlowupOverlap R S.t S.x))).IsMaximal ∧
    (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) (chartBase R S.t S.x S.t) ∈
    (directionPoint R S.t S.x e φ).map (algebraMap (BlowupChart R S.t S.x)
      (BlowupOverlap R S.t S.x)) ∧ ((directionPoint R S.t S.x e φ).map
      (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x))).comap
    (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) =
      directionPoint R S.t S.x e φ := by sorry
