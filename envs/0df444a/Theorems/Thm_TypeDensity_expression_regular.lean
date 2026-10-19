-- Prove2me | Theorems.Thm_TypeDensity_expression_regular
-- name    : TypeDensity.expression_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:45.77239+00:00
-- url     : https://prove2.me/theorems/7ba116c1-eb59-4355-8a45-d6234e29ee63
-- title:
--   The rational function of an expression is regular at every point where it is safe.
-- statement:
--   The rational function of an expression is regular at every point where it is safe.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L144-L147

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_expression_fraction
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

theorem TypeDensity.expression_regular (x : Expr) (q : ℚ) (hx : x.safe q) :
    RegularAt x.rational q := by sorry
