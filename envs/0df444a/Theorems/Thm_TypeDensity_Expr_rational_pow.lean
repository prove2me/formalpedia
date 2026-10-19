-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_pow
-- name    : TypeDensity.Expr.rational_pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:48.767172+00:00
-- url     : https://prove2.me/theorems/5d032e9d-351f-44b3-9c26-73b39c81eb23
-- title:
--   `Expr.rational` commutes with powers.
-- statement:
--   `Expr.rational` commutes with powers.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L907-L913

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_const
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

theorem TypeDensity.Expr.rational_pow (x : Expr) (n : ℕ) : (Expr.pow x n).rational = x.rational ^ n := by sorry
