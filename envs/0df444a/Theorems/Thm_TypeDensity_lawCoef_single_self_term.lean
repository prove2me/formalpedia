-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_single_self_term
-- name    : TypeDensity.lawCoef_single_self_term
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:24.276039+00:00
-- url     : https://prove2.me/theorems/3cb43d65-5318-48ed-afcd-4cc7bf3e48bb
-- title:
--   The self-pattern term of the recursion of `S(a;n)` (`n ≥ 2`) is `q^{-tri n} · q · F_{S(a;n)}`.
-- statement:
--   The self-pattern term of the recursion of `S(a;n)` (`n ≥ 2`) is `q^{-tri n} · q · F_{S(a;n)}`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L993-L1043

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawCoef_single_term
import Theorems.Thm_TypeDensity_rational_divisorProbability_single
import Theorems.Thm_TypeDensity_selfPattern_single_iff
import Theorems.Thm_TypeDensity_Expr_rational_add
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_rational_divisorCount
import Theorems.Thm_TypeDensity_adamsCoef_one
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_qpow_one
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

theorem TypeDensity.lawCoef_single_self_term (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n)
    (P : TangentPattern (State.single a n).degree) (hP : Allowed (State.single a n) P)
    (hself : SelfPattern (State.single a n) P) :
    lawCoef (lawScale (.mul (tangentCount (State.single a n) P)
        (divisorProbability (State.single a n) P.d.val))
        (lawProd ((children (State.single a n) P).map fun z ↦ lawDescend z.1 (stateLaw z.2)))) =
        qpow (-(tri n : ℤ)) * (qpow 1 * lawCoef (stateLaw (State.single a n))) := by sorry
