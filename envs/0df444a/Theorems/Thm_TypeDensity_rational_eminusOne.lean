-- Prove2me | Theorems.Thm_TypeDensity_rational_eminusOne
-- name    : TypeDensity.rational_eminusOne
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:30.415181+00:00
-- url     : https://prove2.me/theorems/5702062b-e892-4558-bf42-d6703bd24191
-- title:
--   The rational function of `eminusOne` is `q - 1`.
-- statement:
--   The rational function of `eminusOne` is `q - 1`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L926-L931

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_Expr_rational_sub
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

theorem TypeDensity.rational_eminusOne : eminusOne.rational = (RatFunc.X : RatFunc ℚ) - 1 := by sorry
