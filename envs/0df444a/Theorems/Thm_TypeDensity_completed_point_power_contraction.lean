-- Prove2me | Theorems.Thm_TypeDensity_completed_point_power_contraction
-- name    : TypeDensity.completed_point_power_contraction
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:33.806764+00:00
-- url     : https://prove2.me/theorems/27bad307-77b1-464e-aa7a-a3de5dd27d1d
-- title:
--   If `m̂^L ⊆ J` in the completed local ring at a maximal ideal `P`, then `P^L` is contained in the contraction of `J`.
-- statement:
--   If `m̂^L ⊆ J` in the completed local ring at a maximal ideal `P`, then `P^L` is contained in the contraction of `J`.
-- source:
--   TypeDensity/Blowup/Charts.lean#L1096-L1106

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.completed_point_power_contraction (A : Type) [CommRing A] (P : Ideal A) [P.IsMaximal]
    (L : ℕ) (J : Ideal (CompletedLocalAt A P)) (hJ : ((IsLocalRing.maximalIdeal
    (Localization.AtPrime P)).map (localCompletionMap (Localization.AtPrime P))) ^ L ≤ J) :
    P^L ≤ J.comap (completedPointMap A P) := by sorry
