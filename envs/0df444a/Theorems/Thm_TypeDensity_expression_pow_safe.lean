-- Prove2me | Theorems.Thm_TypeDensity_expression_pow_safe
-- name    : TypeDensity.expression_pow_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:12.826596+00:00
-- url     : https://prove2.me/theorems/b6a00084-83a3-4d9d-88a9-af44b7083b28
-- title:
--   A formal power of a safe expression is safe.
-- statement:
--   A formal power of a safe expression is safe.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L76-L81

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

theorem TypeDensity.expression_pow_safe (x : Expr) (q : ℚ) (n : ℕ) (hx : x.safe q) :
    (x.pow n).safe q := by sorry
