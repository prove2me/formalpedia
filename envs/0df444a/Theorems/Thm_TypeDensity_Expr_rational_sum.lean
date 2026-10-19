-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_sum
-- name    : TypeDensity.Expr.rational_sum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:40.538015+00:00
-- url     : https://prove2.me/theorems/e063ead8-5fdf-4036-9d14-47f533df5e62
-- title:
--   `Expr.rational` is additive on sums of well-formed expressions.
-- statement:
--   `Expr.rational` is additive on sums of well-formed expressions.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L888-L896

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_rational_add
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

theorem TypeDensity.Expr.rational_sum {xs : List Expr} (h : ∀ z ∈ xs, z.wf) :
    (Expr.sum xs).rational = (xs.map Expr.rational).sum := by sorry
