-- Prove2me | Theorems.Thm_TypeDensity_qmul_assoc
-- name    : TypeDensity.qmul_assoc
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:23.500033+00:00
-- url     : https://prove2.me/theorems/405bc699-1624-4d6f-8a99-1ca25d6fa0fe
-- title:
--   The twisted product is associative.
-- statement:
--   The twisted product is associative.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L516-L557

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_qpow_add
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

theorem TypeDensity.qmul_assoc (U V W : QSer) :
    qmul (qmul U V) W = qmul U (qmul V W) := by sorry
