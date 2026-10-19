-- Prove2me | Theorems.Thm_TypeDensity_SCongr_of_eq
-- name    : TypeDensity.SCongr.of_eq
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:57.934618+00:00
-- url     : https://prove2.me/theorems/2e85556f-707d-4a52-9541-a8418353d3a5
-- title:
--   Equal series are congruent.
-- statement:
--   Equal series are congruent.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L843-L844

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.SCongr.of_eq {n : ℕ} {f g : Ser} (h : f = g) : SCongr n f g := by sorry
