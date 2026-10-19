-- Prove2me | Theorems.Thm_TypeDensity_QCongr_mono
-- name    : TypeDensity.QCongr.mono
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:50.224808+00:00
-- url     : https://prove2.me/theorems/f6f5187e-cd3d-42d8-8830-95679d2e5c01
-- title:
--   Congruence of contact series through degree `j` implies congruence through any `i ≤ j`.
-- statement:
--   Congruence of contact series through degree `j` implies congruence through any `i ≤ j`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L768-L770

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
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

theorem TypeDensity.QCongr.mono {i j : ℕ} {U V : QSer} (h : QCongr j U V) (hij : i ≤ j) : QCongr i U V := by sorry
