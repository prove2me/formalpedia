-- Prove2me | Theorems.Thm_TypeDensity_qdagger_qminus
-- name    : TypeDensity.qdagger_qminus
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:21:47.34801+00:00
-- url     : https://prove2.me/theorems/a5c42f77-0f28-42c1-b2f3-c03b7c8b6540
-- title:
--   `†` commutes with `ι₋`.
-- statement:
--   `†` commutes with `ι₋`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L490-L499

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_two_mul_chooseTwo
import Theorems.Thm_TypeDensity_qpow_add
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_recipCoef_scalar
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

theorem TypeDensity.qdagger_qminus (U : QSer) : qdagger (qminus U) = qminus (qdagger U) := by sorry
