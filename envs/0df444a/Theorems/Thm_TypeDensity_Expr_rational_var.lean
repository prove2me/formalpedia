-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_var
-- name    : TypeDensity.Expr.rational_var
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:52.633348+00:00
-- url     : https://prove2.me/theorems/6a7e7c17-478d-4bbe-b74b-044d6057f9c9
-- title:
--   The rational function of the variable is `q`.
-- statement:
--   The rational function of the variable is `q`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L764-L766

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

theorem TypeDensity.Expr.rational_var : Expr.var.rational = (RatFunc.X : RatFunc ℚ) := by sorry
