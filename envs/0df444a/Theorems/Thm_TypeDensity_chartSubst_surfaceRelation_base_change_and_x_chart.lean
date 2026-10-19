-- Prove2me | Theorems.Thm_TypeDensity_chartSubst_surfaceRelation_base_change_and_x_chart
-- name    : TypeDensity.chartSubst_surfaceRelation_base_change_and_x_chart
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:07.712318+00:00
-- url     : https://prove2.me/theorems/2cfef194-a89e-4694-b1b1-81a26e52acc4
-- title:
--   The surface relation after the t-chart substitution at a unit `θ` (with base change) and after the x-chart substitution is again a surface relation.
-- statement:
--   The surface relation after the t-chart substitution at a unit `θ` (with base change) and after the x-chart substitution is again a surface relation.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L652-L673

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
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

theorem TypeDensity.chartSubst_surfaceRelation_base_change_and_x_chart (O O' : Type) [CommRing O] [CommRing O']
    (ρ : O →+* O') (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    (∀ (θ : O') (hθ : IsUnit θ), chartSubst O' θ
      (MvPowerSeries.map ρ (surfaceRelation O pi u a b)) =
      surfaceRelation O' (ρ pi) (substUnit O' θ (baseChangeUnit O ρ u) * shiftUnit O' θ hθ ^ b)
      (a + b) 0) ∧
    xChartSubst O (surfaceRelation O pi u a b) =
    surfaceRelation O pi (xSubstUnit O u) (a + b) a := by sorry
