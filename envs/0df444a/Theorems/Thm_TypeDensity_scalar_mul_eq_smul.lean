-- Prove2me | Theorems.Thm_TypeDensity_scalar_mul_eq_smul
-- name    : TypeDensity.scalar_mul_eq_smul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:53.769756+00:00
-- url     : https://prove2.me/theorems/a3b16142-869c-4155-a6ea-76e71fae5ded
-- title:
--   Multiplication by `scalar r` is the `ℚ(q)`-scalar action.
-- statement:
--   Multiplication by `scalar r` is the `ℚ(q)`-scalar action.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L131-L133

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_scalar_eq_algebraMap
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

theorem TypeDensity.scalar_mul_eq_smul (r : RatFunc ℚ) (x : Coef) : scalar r * x = r • x := by sorry
