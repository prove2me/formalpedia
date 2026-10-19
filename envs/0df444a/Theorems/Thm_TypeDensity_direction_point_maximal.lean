-- Prove2me | Theorems.Thm_TypeDensity_direction_point_maximal
-- name    : TypeDensity.direction_point_maximal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:32.786173+00:00
-- url     : https://prove2.me/theorems/5fa2949f-1a11-485a-b87d-7de6fc240bd3
-- title:
--   The direction point of an affine direction `φ` is a maximal ideal containing `t`;
-- statement:
--   The direction point of an affine direction `φ` is a maximal ideal containing `t`; it contains the slope iff `φ` is the zero direction, maps onto `(φ)` in the exceptional fibre, has `R`-length `deg φ`, and depends injectively on `φ`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L503-L573

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

theorem TypeDensity.direction_point_maximal (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R] (S : SurfaceData O R)
    (e : (BlowupChart R S.t S.x ⧸ chartExceptional R S.t S.x) ≃+* Polynomial
      (IsLocalRing.ResidueField R)) (he : ∀ r : R,
      e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartBase R S.t S.x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartSlope R S.t S.x)) = Polynomial.X)
    (φ : AffineDirection (IsLocalRing.ResidueField R)) :
    (directionPoint R S.t S.x e φ).IsMaximal ∧
    chartBase R S.t S.x S.t ∈ directionPoint R S.t S.x e φ ∧
    (chartSlope R S.t S.x ∈ directionPoint R S.t S.x e φ ↔ φ =
      zeroAffine (IsLocalRing.ResidueField R)) ∧
    ((directionPoint R S.t S.x e φ).map (Ideal.Quotient.mk (chartExceptional R S.t S.x))).map e =
    Ideal.span {φ.val} ∧ Module.length R (BlowupChart R S.t S.x ⧸ directionPoint R S.t S.x e φ) =
    (φ.val.natDegree : ℕ∞) ∧ Function.Injective (directionPoint R S.t S.x e) := by sorry
