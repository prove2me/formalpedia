-- Prove2me | Theorems.Thm_TypeDensity_SCongr_logSer
-- name    : TypeDensity.SCongr.logSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:31.327352+00:00
-- url     : https://prove2.me/theorems/b7ff4b5d-80be-499a-b061-c1f3f1558be0
-- title:
--   `log` preserves congruence through degree `n` (on series with constant term `1`).
-- statement:
--   `log` preserves congruence through degree `n` (on series with constant term `1`).
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L913-L918

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_scongr_subst
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

theorem TypeDensity.SCongr.logSer {n : ℕ} {u v : Ser} (hu : PowerSeries.constantCoeff u = 1)
    (hv : PowerSeries.constantCoeff v = 1) (huv : SCongr n u v) :
    SCongr n (TypeDensity.logSer u) (TypeDensity.logSer v) := by sorry
