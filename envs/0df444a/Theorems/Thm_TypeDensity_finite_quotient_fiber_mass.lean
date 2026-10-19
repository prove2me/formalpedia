-- Prove2me | Theorems.Thm_TypeDensity_finite_quotient_fiber_mass
-- name    : TypeDensity.finite_quotient_fiber_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:11.512786+00:00
-- url     : https://prove2.me/theorems/dfc11f0f-1730-4b35-92b3-d279ecca9cc1
-- title:
--   Under an invariant probability measure, each fibre of a surjection onto a finite group has mass `1/|Q|`.
-- statement:
--   Under an invariant probability measure, each fibre of a surjection onto a finite group has mass `1/|Q|`.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L234-L263

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

theorem TypeDensity.finite_quotient_fiber_mass (G Q : Type) [AddCommGroup G] [AddCommGroup Q] [Finite Q]
    [MeasurableSpace G] [MeasurableAdd G] (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddLeftInvariant mu]
    (pi : G →+ Q) (hpi : Function.Surjective pi) (hm : ∀ a, MeasurableSet {x | pi x = a}) (a : Q) :
    mu {x | pi x = a} = (Nat.card Q : ℝ≥0∞)⁻¹ := by sorry
