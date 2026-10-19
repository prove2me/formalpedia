-- Prove2me | Theorems.Thm_TypeDensity_exists_unique_selfPattern_single
-- name    : TypeDensity.exists_unique_selfPattern_single
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:22.830548+00:00
-- url     : https://prove2.me/theorems/bb519bba-f589-43f6-aabf-5d40b347d50f
-- title:
--   For `n ≥ 2`, `S(a;n)` has exactly one allowed self pattern.
-- statement:
--   For `n ≥ 2`, `S(a;n)` has exactly one allowed self pattern.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L590-L642

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_selfPattern_single_iff
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

theorem TypeDensity.exists_unique_selfPattern_single (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n) :
    ∃ P₀ : TangentPattern (State.single a n).degree, Allowed (State.single a n) P₀ ∧
        SelfPattern (State.single a n) P₀ ∧ ∀ Q : TangentPattern (State.single a n).degree,
        Allowed (State.single a n) Q → SelfPattern (State.single a n) Q → Q = P₀ := by sorry
