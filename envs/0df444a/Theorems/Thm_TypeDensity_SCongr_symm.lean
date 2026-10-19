-- Prove2me | Theorems.Thm_TypeDensity_SCongr_symm
-- name    : TypeDensity.SCongr.symm
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:02.78835+00:00
-- url     : https://prove2.me/theorems/6e55ad1d-9106-45d2-97f4-3dc5722a5ac3
-- title:
--   Congruence of series is symmetric.
-- statement:
--   Congruence of series is symmetric.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L846-L848

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

theorem TypeDensity.SCongr.symm {n : ℕ} {f g : Ser} (h : SCongr n f g) : SCongr n g f := by sorry
