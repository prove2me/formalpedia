-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_add
-- name    : TypeDensity.Expr.rational_add
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:08.522809+00:00
-- url     : https://prove2.me/theorems/aa29af22-1fcc-45d3-a569-77b7f0ba702e
-- title:
--   `Expr.rational` is additive on well-formed expressions.
-- statement:
--   `Expr.rational` is additive on well-formed expressions.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L741-L748

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_fraction_snd_ne_zero
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

theorem TypeDensity.Expr.rational_add {x y : Expr} (hx : x.wf) (hy : y.wf) :
    (Expr.add x y).rational = x.rational + y.rational := by sorry
