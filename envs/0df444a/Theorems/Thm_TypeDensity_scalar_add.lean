-- Prove2me | Theorems.Thm_TypeDensity_scalar_add
-- name    : TypeDensity.scalar_add
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:57.259411+00:00
-- url     : https://prove2.me/theorems/9f63b4b9-bd01-451f-a69e-84a15c11f198
-- title:
--   `scalar : ℚ(q) → Coef` is additive.
-- statement:
--   `scalar : ℚ(q) → Coef` is additive.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L119-L121

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

theorem TypeDensity.scalar_add (f g : RatFunc ℚ) : scalar (f + g) = scalar f + scalar g := by sorry
