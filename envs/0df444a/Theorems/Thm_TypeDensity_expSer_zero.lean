-- Prove2me | Theorems.Thm_TypeDensity_expSer_zero
-- name    : TypeDensity.expSer_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:43.230983+00:00
-- url     : https://prove2.me/theorems/1f68e75f-e524-41d1-bf8c-551d94f3e5fe
-- title:
--   `exp 0 = 1`.
-- statement:
--   `exp 0 = 1`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L439-L443

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

theorem TypeDensity.expSer_zero : expSer (0 : Ser) = 1 := by sorry
