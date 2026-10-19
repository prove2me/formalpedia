-- Prove2me | Theorems.Thm_TypeDensity_qpow_neg_mul_qpow
-- name    : TypeDensity.qpow_neg_mul_qpow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:21.874046+00:00
-- url     : https://prove2.me/theorems/a6add502-5b3b-4e7d-b804-40e8e56c01da
-- title:
--   `q^{-j} q^j = 1`.
-- statement:
--   `q^{-j} q^j = 1`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L157-L159

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_qpow_add
import Theorems.Thm_TypeDensity_qpow_zero
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

theorem TypeDensity.qpow_neg_mul_qpow (j : ℤ) : qpow (-j) * qpow j = 1 := by sorry
