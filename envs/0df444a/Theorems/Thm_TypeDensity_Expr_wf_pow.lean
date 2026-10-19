-- Prove2me | Theorems.Thm_TypeDensity_Expr_wf_pow
-- name    : TypeDensity.Expr.wf_pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:44.720633+00:00
-- url     : https://prove2.me/theorems/cbaab6ca-ed73-499a-a7c3-54fbd75f30b5
-- title:
--   Powers of well-formed expressions are well formed.
-- statement:
--   Powers of well-formed expressions are well formed.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L694-L698

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

theorem TypeDensity.Expr.wf_pow {x : Expr} (hx : x.wf) (k : ℕ) : (Expr.pow x k).wf := by sorry
