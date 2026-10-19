-- Prove2me | Theorems.Thm_TypeDensity_recipCoef_scalar
-- name    : TypeDensity.recipCoef_scalar
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:23.975083+00:00
-- url     : https://prove2.me/theorems/dccb1c47-ebe1-4752-b922-d44aafaa8c69
-- title:
--   `v` on scalars is `q ↦ q⁻¹`.
-- statement:
--   `v` on scalars is `q ↦ q⁻¹`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L76-L78

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipCoef_single
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

theorem TypeDensity.recipCoef_scalar (f : RatFunc ℚ) : recipCoef (scalar f) = scalar (recipRat f) := by sorry
