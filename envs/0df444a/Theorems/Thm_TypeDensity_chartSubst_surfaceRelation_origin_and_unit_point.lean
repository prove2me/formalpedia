-- Prove2me | Theorems.Thm_TypeDensity_chartSubst_surfaceRelation_origin_and_unit_point
-- name    : TypeDensity.chartSubst_surfaceRelation_origin_and_unit_point
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:13.522971+00:00
-- url     : https://prove2.me/theorems/c89320ca-5f2e-431c-baa3-a4786f027055
-- title:
--   The surface relation after the t-chart substitution at the origin and at a unit point is again a surface relation.
-- statement:
--   The surface relation after the t-chart substitution at the origin and at a unit point is again a surface relation.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L675-L697

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_chartSubst_surfaceRelation
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

theorem TypeDensity.chartSubst_surfaceRelation_origin_and_unit_point (O : Type) [CommRing O] (pi : O)
    (u : (TwoSeries O)ˣ) (a b : ℕ) :
    chartSubst O 0 (surfaceRelation O pi u a b) = surfaceRelation O pi (substUnit O 0 u) (a + b) b ∧
    ∀ (α : O) (hα : IsUnit α), chartSubst O α (surfaceRelation O pi u a b) =
    surfaceRelation O pi (substUnit O α u * shiftUnit O α hα ^ b) (a + b) 0 := by sorry
