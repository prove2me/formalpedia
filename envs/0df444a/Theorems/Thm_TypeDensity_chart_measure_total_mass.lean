-- Prove2me | Theorems.Thm_TypeDensity_chart_measure_total_mass
-- name    : TypeDensity.chart_measure_total_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:06.835706+00:00
-- url     : https://prove2.me/theorems/dd9814d4-841b-4389-9e9e-5b89c9e8379b
-- title:
--   A chart measure with measurable chart map has total mass one.
-- statement:
--   A chart measure with measurable chart map has total mass one.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L1236-L1246

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Theorems.Thm_TypeDensity_coefficient_measure_probability
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
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.chart_measure_total_mass (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (n : ℕ) (c : IdealChart O R pi n)
    (hc : Measurable (coordinateIdeal pi c.f c.b)) :
    chartMeasure O R pi n c Set.univ = 1 := by sorry
