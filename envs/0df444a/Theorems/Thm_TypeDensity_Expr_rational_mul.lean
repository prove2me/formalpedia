-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_mul
-- name    : TypeDensity.Expr.rational_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:54.000993+00:00
-- url     : https://prove2.me/theorems/3586a810-d601-40e6-a37e-ff540374f4b4
-- title:
--   `Expr.rational` is multiplicative.
-- statement:
--   `Expr.rational` is multiplicative.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L750-L753

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.Expr.rational_mul (x y : Expr) : (Expr.mul x y).rational = x.rational * y.rational := by sorry
