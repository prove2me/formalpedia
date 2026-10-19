-- Prove2me | Theorems.Thm_TypeDensity_expression_prod_eval
-- name    : TypeDensity.expression_prod_eval
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:15.855766+00:00
-- url     : https://prove2.me/theorems/ae18a695-0f66-4872-9e0f-6782ff3ad7df
-- title:
--   Evaluation of a formal product is the product of the evaluations.
-- statement:
--   Evaluation of a formal product is the product of the evaluations.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L83-L86

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

theorem TypeDensity.expression_prod_eval (xs : List Expr) (q : ℚ) :
    (Expr.prod xs).eval q = (xs.map (Expr.eval q)).prod := by sorry
