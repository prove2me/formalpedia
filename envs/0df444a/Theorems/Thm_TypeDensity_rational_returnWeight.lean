-- Prove2me | Theorems.Thm_TypeDensity_rational_returnWeight
-- name    : TypeDensity.rational_returnWeight
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:58.451984+00:00
-- url     : https://prove2.me/theorems/a8ac0dcc-05e0-401f-97d8-8cb6aaf92de8
-- title:
--   The return weight is `q · q^{-tri c}`.
-- statement:
--   The return weight is `q · q^{-tri c}`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L430-L434

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_Expr_rational_pow
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

theorem TypeDensity.rational_returnWeight (c : ℕ) :
    (returnWeight c).rational = (RatFunc.X : RatFunc ℚ) * ((RatFunc.X : RatFunc ℚ) ^ tri c)⁻¹ := by sorry
