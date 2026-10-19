-- Prove2me | Theorems.Thm_TypeDensity_completed_point_transport_left
-- name    : TypeDensity.completed_point_transport_left
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:39.316432+00:00
-- url     : https://prove2.me/theorems/f8c5e825-57b9-4f4c-9189-e76e883b556b
-- title:
--   At a prime of the overlap, the completed local ring of the overlap is the completed local ring of the chart at the contracted prime.
-- statement:
--   At a prime of the overlap, the completed local ring of the overlap is the completed local ring of the chart at the contracted prime.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L907-L929

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
import Theorems.Thm_TypeDensity_local_completion_transport
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

theorem TypeDensity.completed_point_transport_left (R : Type) [CommRing R] (t x : R)
    [IsNoetherianRing (BlowupChart R t x)] (Q : Ideal (BlowupOverlap R t x)) [Q.IsPrime] :
    ∃ Φ : CompletedLocalAt (BlowupOverlap R t x) Q ≃+* CompletedLocalAt (BlowupChart R t x)
    (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))), ∀ a : BlowupChart R t x, Φ
    (completedPointMap (BlowupOverlap R t x) Q
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a)) = completedPointMap
    (BlowupChart R t x) (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) a := by sorry
