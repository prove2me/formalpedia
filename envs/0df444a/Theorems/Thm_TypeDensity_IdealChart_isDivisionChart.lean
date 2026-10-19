-- Prove2me | Theorems.Thm_TypeDensity_IdealChart_isDivisionChart
-- name    : TypeDensity.IdealChart.isDivisionChart
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:19.656591+00:00
-- url     : https://prove2.me/theorems/87dc2f4d-cdc6-4990-ad61-3bb0185ae4e8
-- title:
--   The centre and representatives of an ideal chart form a division chart.
-- statement:
--   The centre and representatives of an ideal chart form a division chart.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L186-L190

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal
variable (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
variable {O R}

theorem TypeDensity.IdealChart.isDivisionChart {pi : O} {n : ℕ} (C : IdealChart O R pi n) :
    IsDivisionChart O R pi C.f C.b := by sorry
