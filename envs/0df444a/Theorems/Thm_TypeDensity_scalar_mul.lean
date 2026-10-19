-- Prove2me | Theorems.Thm_TypeDensity_scalar_mul
-- name    : TypeDensity.scalar_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:45.289987+00:00
-- url     : https://prove2.me/theorems/c4599ada-81df-4235-bc23-601b780636bb
-- title:
--   `scalar : ℚ(q) → Coef` is multiplicative.
-- statement:
--   `scalar : ℚ(q) → Coef` is multiplicative.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L115-L117

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

theorem TypeDensity.scalar_mul (f g : RatFunc ℚ) : scalar (f * g) = scalar f * scalar g := by sorry
