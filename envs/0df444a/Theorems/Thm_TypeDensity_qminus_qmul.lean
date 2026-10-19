-- Prove2me | Theorems.Thm_TypeDensity_qminus_qmul
-- name    : TypeDensity.qminus_qmul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:17.701029+00:00
-- url     : https://prove2.me/theorems/bdfb306f-5c00-4e43-9d07-1c69eea18cf6
-- title:
--   `ι₋` is multiplicative for the twisted product.
-- statement:
--   `ι₋` is multiplicative for the twisted product.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L869-L871

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_qplus_qmul
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

theorem TypeDensity.qminus_qmul (U V : QSer) : qminus (qmul U V) = qmul (qminus U) (qminus V) := by sorry
