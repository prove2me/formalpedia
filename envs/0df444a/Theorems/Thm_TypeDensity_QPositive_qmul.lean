-- Prove2me | Theorems.Thm_TypeDensity_QPositive_qmul
-- name    : TypeDensity.QPositive.qmul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:49.226589+00:00
-- url     : https://prove2.me/theorems/548563e4-f5f9-487a-9c64-b321c68990ac
-- title:
--   Positivity (vanishing on the axes away from `(0,0)`) is preserved by the twisted product.
-- statement:
--   Positivity (vanishing on the axes away from `(0,0)`) is preserved by the twisted product.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L163-L181

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

theorem TypeDensity.QPositive.qmul {U V : QSer} (hU : QPositive U) (hV : QPositive V) :
    QPositive (qmul U V) := by sorry
