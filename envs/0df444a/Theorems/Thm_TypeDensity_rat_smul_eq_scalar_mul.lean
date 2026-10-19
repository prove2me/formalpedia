-- Prove2me | Theorems.Thm_TypeDensity_rat_smul_eq_scalar_mul
-- name    : TypeDensity.rat_smul_eq_scalar_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:11.924967+00:00
-- url     : https://prove2.me/theorems/6b47b9ec-c191-4e09-81ea-0b1b94e3a23c
-- title:
--   The `ℚ`-scalar action on `Coef` is multiplication by the constant scalar.
-- statement:
--   The `ℚ`-scalar action on `Coef` is multiplication by the constant scalar.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L135-L139

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

theorem TypeDensity.rat_smul_eq_scalar_mul (q : ℚ) (x : Coef) : q • x = scalar (RatFunc.C q) * x := by sorry
