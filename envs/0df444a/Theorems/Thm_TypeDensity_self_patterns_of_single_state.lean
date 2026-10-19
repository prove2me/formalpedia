-- Prove2me | Theorems.Thm_TypeDensity_self_patterns_of_single_state
-- name    : TypeDensity.self_patterns_of_single_state
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:56.006425+00:00
-- url     : https://prove2.me/theorems/4c7c61e7-2105-4b8d-b9ed-aa8663c05025
-- title:
--   A single-branch state `S(a;
-- statement:
--   A single-branch state `S(a; c)` with `c ≥ 2` has exactly one self pattern (of multiplicity `d = c`, with the state itself as only child), whose tangent count at `q` is `q`.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L177-L191

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_expression_prod_eval
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
open scoped Classical

theorem TypeDensity.self_patterns_of_single_state (a c q : ℕ) (ha : 0 < a) (hc : 2 ≤ c) :
    (∀ P : TangentPattern (State.single a c).degree, Allowed (State.single a c) P →
        SelfPattern (State.single a c) P →
          P.d.val = c ∧ children (State.single a c) P = [(1, State.single a c)]) ∧
      (((allowedPatterns (State.single a c)).toList.filter (SelfPattern (State.single a c))).map
        fun P ↦ (tangentCount (State.single a c) P).eval q).sum = q := by sorry
