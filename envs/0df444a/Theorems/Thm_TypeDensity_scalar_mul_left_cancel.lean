-- Prove2me | Theorems.Thm_TypeDensity_scalar_mul_left_cancel
-- name    : TypeDensity.scalar_mul_left_cancel
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:38.680702+00:00
-- url     : https://prove2.me/theorems/b3dba214-3467-438d-8f18-597201a34e60
-- title:
--   Multiplication by a nonzero scalar `scalar w` is injective on `Coef`.
-- statement:
--   Multiplication by a nonzero scalar `scalar w` is injective on `Coef`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L828-L833

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_scalar_one
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

theorem TypeDensity.scalar_mul_left_cancel {w : RatFunc ℚ} (hw : w ≠ 0) {x y : Coef}
    (h : scalar w * x = scalar w * y) : x = y := by sorry
