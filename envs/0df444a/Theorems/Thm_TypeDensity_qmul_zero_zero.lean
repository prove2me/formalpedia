-- Prove2me | Theorems.Thm_TypeDensity_qmul_zero_zero
-- name    : TypeDensity.qmul_zero_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:29.303991+00:00
-- url     : https://prove2.me/theorems/f14b6169-cfa3-4b5c-9897-83f0a010b47d
-- title:
--   The constant term of a twisted product: `(U V)₀₀ = U₀₀ V₀₀`.
-- statement:
--   The constant term of a twisted product: `(U V)₀₀ = U₀₀ V₀₀`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L208-L210

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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

theorem TypeDensity.qmul_zero_zero (U V : QSer) : (qmul U V) 0 0 = U 0 0 * V 0 0 := by sorry
