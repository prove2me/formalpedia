-- Prove2me | Theorems.Thm_TypeDensity_scalar_eq_algebraMap
-- name    : TypeDensity.scalar_eq_algebraMap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:45.328075+00:00
-- url     : https://prove2.me/theorems/b454f463-4be8-4d2f-a992-2a3e533b2cb9
-- title:
--   `scalar` is the algebra map `ℚ(q) → Coef`.
-- statement:
--   `scalar` is the algebra map `ℚ(q) → Coef`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L126-L129

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

theorem TypeDensity.scalar_eq_algebraMap (f : RatFunc ℚ) : scalar f = algebraMap (RatFunc ℚ) Coef f := by sorry
