-- Prove2me | Theorems.Thm_TypeDensity_sum_allowedPatterns_single
-- name    : TypeDensity.sum_allowedPatterns_single
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:20.490489+00:00
-- url     : https://prove2.me/theorems/9cfe53bb-6a1b-4961-a4f2-604b7ce066f3
-- title:
--   A sum over the allowed tangent patterns of `S(a;n)` depending only on the divisor degree `d`, the tangent depth `r`, and the off-boundary pattern, reindexed as a sum over `d`, `r` and patterns of weig
-- statement:
--   A sum over the allowed tangent patterns of `S(a;n)` depending only on the divisor degree `d`, the tangent depth `r`, and the off-boundary pattern can be reindexed as a sum over `d`, `r` and patterns of weight `d - r`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L480-L494

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_sum_allowedPatterns_reindex
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

theorem TypeDensity.sum_allowedPatterns_single (a n : ℕ) (ha : 0 < a)
    (F : ℕ → ℕ → Pattern (State.single a n).degree → Coef) :
    ∑ P ∈ allowedPatterns (State.single a n), F P.d.val P.rt.val P.other =
      ∑ d ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (d + 1), (if ((0 < r ↔ d < n) ∧ r ≤ d) then
        ∑ m ∈ (Finset.univ : Finset (Pattern (State.single a n).degree)).filter
          (fun m ↦ patternWeight m = d - r), F d r m else 0) := by sorry
