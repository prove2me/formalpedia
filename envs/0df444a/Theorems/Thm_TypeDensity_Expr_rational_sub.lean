-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_sub
-- name    : TypeDensity.Expr.rational_sub
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:47.441506+00:00
-- url     : https://prove2.me/theorems/ba904e6e-fb85-410e-b75b-ac46c844f0b7
-- title:
--   `Expr.rational` is additive on differences of well-formed expressions.
-- statement:
--   `Expr.rational` is additive on differences of well-formed expressions.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L919-L924

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_rational_add
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

theorem TypeDensity.Expr.rational_sub {x y : Expr} (hx : x.wf) (hy : y.wf) :
    (Expr.sub x y).rational = x.rational - y.rational := by sorry
