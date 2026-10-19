-- Prove2me | Theorems.Thm_TypeDensity_expression_fraction
-- name    : TypeDensity.expression_fraction
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:06.674988+00:00
-- url     : https://prove2.me/theorems/043464af-776a-4aef-bac8-80f5a1a1f939
-- title:
--   At a point where `x` is safe, the denominator of `x.fraction` does not vanish and `x` evaluates to numerator over denominator.
-- statement:
--   At a point where `x` is safe, the denominator of `x.fraction` does not vanish and `x` evaluates to numerator over denominator.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L119-L142

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

theorem TypeDensity.expression_fraction (x : Expr) (q : ℚ) (hx : x.safe q) :
    x.fraction.2.eval q ≠ 0 ∧ x.eval q = x.fraction.1.eval q / x.fraction.2.eval q := by sorry
