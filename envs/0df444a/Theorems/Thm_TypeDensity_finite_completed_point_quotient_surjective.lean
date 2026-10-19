-- Prove2me | Theorems.Thm_TypeDensity_finite_completed_point_quotient_surjective
-- name    : TypeDensity.finite_completed_point_quotient_surjective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:04:09.330985+00:00
-- url     : https://prove2.me/theorems/d887133a-2aec-4160-bc4f-486e4c20ad7d
-- title:
--   At a maximal ideal `P` of a Noetherian ring `A`, an ideal `J` of the completed local ring containing a power of its maximal ideal makes `A → Â_P → Â_P/J` surjective.
-- statement:
--   At a maximal ideal `P` of a Noetherian ring `A`, an ideal `J` of the completed local ring containing a power of its maximal ideal makes `A → Â_P → Â_P/J` surjective.
-- source:
--   TypeDensity/Unramified/LocalDescent.lean#L155-L188

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_local_completion_finite_quotient
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.finite_completed_point_quotient_surjective (A : Type) [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsMaximal] (L : ℕ) (J : Ideal (CompletedLocalAt A P))
    (hJ : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P))) ^ L ≤ J) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (completedPointMap A P)) := by sorry
