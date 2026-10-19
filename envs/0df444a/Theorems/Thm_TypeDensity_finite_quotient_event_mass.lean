-- Prove2me | Theorems.Thm_TypeDensity_finite_quotient_event_mass
-- name    : TypeDensity.finite_quotient_event_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:28.125767+00:00
-- url     : https://prove2.me/theorems/dafae373-bef2-4e2a-8a04-5fbd84309785
-- title:
--   Under an invariant probability measure, the preimage of `S ⊆ Q` under a surjection onto a finite group has mass `|S|/|Q|`.
-- statement:
--   Under an invariant probability measure, the preimage of `S ⊆ Q` under a surjection onto a finite group has mass `|S|/|Q|`.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L305-L321

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_finite_quotient_fiber_mass
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

theorem TypeDensity.finite_quotient_event_mass (G Q : Type) [AddCommGroup G] [AddCommGroup Q] [Finite Q]
    [MeasurableSpace G] [MeasurableAdd G] (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddLeftInvariant mu]
    (pi : G →+ Q) (hpi : Function.Surjective pi) (hm : ∀ a, MeasurableSet {x | pi x = a})
    (S : Set Q) :
    mu (pi ⁻¹' S) = (Nat.card S : ℝ≥0∞) / Nat.card Q := by sorry
