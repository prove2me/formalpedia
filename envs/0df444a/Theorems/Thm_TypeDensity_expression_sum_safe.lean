-- Prove2me | Theorems.Thm_TypeDensity_expression_sum_safe
-- name    : TypeDensity.expression_sum_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:06.256007+00:00
-- url     : https://prove2.me/theorems/18d4db65-fbbf-46ab-849d-8553fe180b2b
-- title:
--   A formal sum of safe expressions is safe.
-- statement:
--   A formal sum of safe expressions is safe.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L98-L101

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.expression_sum_safe (xs : List Expr) (q : ℚ) (h : ∀ x ∈ xs, x.safe q) :
    (Expr.sum xs).safe q := by sorry
