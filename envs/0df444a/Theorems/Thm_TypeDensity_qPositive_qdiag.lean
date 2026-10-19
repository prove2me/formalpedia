-- Prove2me | Theorems.Thm_TypeDensity_qPositive_qdiag
-- name    : TypeDensity.qPositive_qdiag
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:12.125487+00:00
-- url     : https://prove2.me/theorems/994cfa81-e2db-4ad1-a304-06d75b386c36
-- title:
--   The diagonal substitution of a series is positive.
-- statement:
--   The diagonal substitution of a series is positive.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L203-L206

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

theorem TypeDensity.qPositive_qdiag (f : Ser) : QPositive (qdiag f) := by sorry
