-- Prove2me | Theorems.Thm_TypeDensity_SCongr_pow
-- name    : TypeDensity.SCongr.pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:07.300396+00:00
-- url     : https://prove2.me/theorems/7c6bee98-a544-4175-8fa6-782ec6d7b7bb
-- title:
--   Congruence of series is compatible with powers.
-- statement:
--   Congruence of series is compatible with powers.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L873-L877

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_SCongr_mul
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

theorem TypeDensity.SCongr.pow {n : ℕ} {f g : Ser} (h : SCongr n f g) (p : ℕ) : SCongr n (f ^ p) (g ^ p) := by sorry
