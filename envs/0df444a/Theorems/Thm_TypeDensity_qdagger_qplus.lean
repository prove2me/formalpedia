-- Prove2me | Theorems.Thm_TypeDensity_qdagger_qplus
-- name    : TypeDensity.qdagger_qplus
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:03.976743+00:00
-- url     : https://prove2.me/theorems/84fa1c21-2708-459b-af8a-dce5bde8006e
-- title:
--   `†` commutes with `ι₊`.
-- statement:
--   `†` commutes with `ι₊`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L482-L488

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

theorem TypeDensity.qdagger_qplus (U : QSer) : qdagger (qplus U) = qplus (qdagger U) := by sorry
