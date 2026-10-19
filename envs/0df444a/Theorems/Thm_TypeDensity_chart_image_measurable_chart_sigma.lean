-- Prove2me | Theorems.Thm_TypeDensity_chart_image_measurable_chart_sigma
-- name    : TypeDensity.chart_image_measurable_chart_sigma
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:52.132479+00:00
-- url     : https://prove2.me/theorems/1b07967b-8e56-4ef6-8938-cfd61daf4f71
-- title:
--   The image of a measurable set of coordinates under a division chart is measurable for the chart σ-algebra on ideals.
-- statement:
--   The image of a measurable set of coordinates under a division chart is measurable for the chart σ-algebra on ideals.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L108-L114

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
open scoped ENNReal

theorem TypeDensity.chart_image_measurable_chart_sigma (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    [MeasurableSpace O] (pi : O) (n : ℕ) (f : R) (b : Fin n → R)
    (hchart : IsDivisionChart O R pi f b) (S : Set (Fin n → O)) (hS : MeasurableSet S) :
    @MeasurableSet (Ideal R) (idealChartSigma O R pi) (coordinateIdeal pi f b '' S) := by sorry
