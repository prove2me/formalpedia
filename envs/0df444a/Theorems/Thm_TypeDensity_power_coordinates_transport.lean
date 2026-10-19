-- Prove2me | Theorems.Thm_TypeDensity_power_coordinates_transport
-- name    : TypeDensity.power_coordinates_transport
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:31.399696+00:00
-- url     : https://prove2.me/theorems/6c86f5fe-b492-49d9-8bd9-5b222e7b63bf
-- title:
--   With the topology and σ-algebra transported along the power-basis coordinates, `O[X]/(Φ)` is a compact Hausdorff second-countable Borel topological ring, and the coordinates are a homeomorphism and a
-- statement:
--   With the topology and σ-algebra transported along the power-basis coordinates, `O[X]/(Φ)` is a compact Hausdorff second-countable Borel topological ring, and the coordinates are a homeomorphism and a measurable equivalence.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L868-L917

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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

theorem TypeDensity.power_coordinates_transport (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (Φ : Polynomial O) (hm : Φ.Monic)
    [TopologicalSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hm)
    [MeasurableSpace (AdjoinRoot Φ)]
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hm) :
    IsTopologicalRing (AdjoinRoot Φ) ∧ CompactSpace (AdjoinRoot Φ) ∧ T2Space (AdjoinRoot Φ) ∧
      SecondCountableTopology (AdjoinRoot Φ) ∧ BorelSpace (AdjoinRoot Φ) ∧
      Continuous (powerCoordinates O Φ hm) ∧ Continuous (powerCoordinates O Φ hm).symm ∧
      Measurable (powerCoordinates O Φ hm) ∧ Measurable (powerCoordinates O Φ hm).symm := by sorry
