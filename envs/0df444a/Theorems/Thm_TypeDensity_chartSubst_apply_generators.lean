-- Prove2me | Theorems.Thm_TypeDensity_chartSubst_apply_generators
-- name    : TypeDensity.chartSubst_apply_generators
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:28.190822+00:00
-- url     : https://prove2.me/theorems/99688566-e973-4cd0-ba68-facc6579242a
-- title:
--   Values of the chart substitutions `chartSubst`, `xChartSubst` and `killT` on constants and on the two variables.
-- statement:
--   The chart substitutions fix constants and act on the two variables as follows: `chartSubst` sends `T ↦ T` and `X ↦ T(X + α)`, `xChartSubst` sends `T ↦ TX` and `X ↦ T`, and `killT` sends `T ↦ 0` and `X ↦ X` (with constants mapped to constants).
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L617-L634

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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

theorem TypeDensity.chartSubst_apply_generators (O : Type) [CommRing O] (α : O) :
    (∀ c : O, chartSubst O α (MvPowerSeries.C c) = MvPowerSeries.C c) ∧
    chartSubst O α (axisT O) = axisT O ∧
    chartSubst O α (axisX O) = axisT O * (axisX O + MvPowerSeries.C α) ∧
    (∀ c : O, xChartSubst O (MvPowerSeries.C c) = MvPowerSeries.C c) ∧
    xChartSubst O (axisT O) = axisT O * axisX O ∧ xChartSubst O (axisX O) = axisT O ∧
    (∀ c : O, killT O (MvPowerSeries.C c) = PowerSeries.C c) ∧ killT O (axisT O) = 0 ∧
    killT O (axisX O) = PowerSeries.X := by sorry
