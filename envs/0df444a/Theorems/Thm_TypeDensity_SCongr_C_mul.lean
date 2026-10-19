-- Prove2me | Theorems.Thm_TypeDensity_SCongr_C_mul
-- name    : TypeDensity.SCongr.C_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:52.154386+00:00
-- url     : https://prove2.me/theorems/28654179-6e54-4eeb-9a8d-6b5774017a2a
-- title:
--   Congruence of series is compatible with multiplication by a constant.
-- statement:
--   Congruence of series is compatible with multiplication by a constant.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L868-L871

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

theorem TypeDensity.SCongr.C_mul {n : ℕ} {f g : Ser} (h : SCongr n f g) (a : Coef) :
    SCongr n (PowerSeries.C a * f) (PowerSeries.C a * g) := by sorry
