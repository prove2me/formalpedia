-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_const
-- name    : TypeDensity.Expr.rational_const
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:54.877111+00:00
-- url     : https://prove2.me/theorems/fe519fa7-9845-4fce-96bd-d0e95c2b252f
-- title:
--   The rational function of a constant.
-- statement:
--   The rational function of a constant `r` is `RatFunc.C r`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L760-L762

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

theorem TypeDensity.Expr.rational_const (r : ℚ) : (Expr.const r).rational = RatFunc.C r := by sorry
