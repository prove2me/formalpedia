-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_stateLaw_crossing_comm
-- name    : TypeDensity.lawCoef_stateLaw_crossing_comm
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:26:04.124735+00:00
-- url     : https://prove2.me/theorems/a91ba24c-085f-4a38-8564-f45ffd2d4b63
-- title:
--   The law of a crossing state is symmetric under exchanging the two branches: `F_{T(a,b;c,h)} = F_{T(b,a;h,c)}`.
-- statement:
--   The law of a crossing state is symmetric under exchanging the two branches: `F_{T(a,b;c,h)} = F_{T(b,a;h,c)}`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L564-L588

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_state_law_unfold
import Theorems.Thm_TypeDensity_lawCoef_exitLaw_crossing
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_rational_eminusOne
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

theorem TypeDensity.lawCoef_stateLaw_crossing_comm (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) :
    lawCoef (stateLaw (State.crossing a b c h)) = lawCoef (stateLaw (State.crossing b a h c)) := by sorry
