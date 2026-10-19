-- Prove2me | Theorems.Thm_TypeDensity_sum_allowedPatterns_reindex
-- name    : TypeDensity.sum_allowedPatterns_reindex
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:42.493977+00:00
-- url     : https://prove2.me/theorems/ad3ca68b-6246-4a1c-93ae-bd5f50a48cab
-- title:
--   A sum over the allowed tangent patterns of a state `s` whose summand depends only on the data `(d, rt, rx)` and the off-boundary pattern, reindexed by `d ∈ [1, D]`, `rt, rx ≤ d` and the off-boundary p
-- statement:
--   A sum over the allowed tangent patterns of a state `s` whose summand depends only on the data `(d, rt, rx)` and the off-boundary pattern can be reindexed by `d ∈ [1, D]`, `rt, rx ≤ d` and the off-boundary patterns of weight `d - rt - rx`. Here `D` bounds the divisor degree and `Q` is the boundary condition on `(d, rt, rx)` in the description `hmem` of the allowed patterns.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L551-L601

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.sum_allowedPatterns_reindex (s : State) (D : ℕ) (hD : D ≤ s.degree)
    (Q : ℕ → ℕ → ℕ → Prop) [∀ d rt rx, Decidable (Q d rt rx)]
    (hmem : ∀ P, P ∈ allowedPatterns s ↔ 0 < P.d.val ∧
      P.rt.val + P.rx.val + patternWeight P.other = P.d.val ∧ P.d.val ≤ D ∧
      Q P.d.val P.rt.val P.rx.val)
    (F : ℕ → ℕ → ℕ → Pattern s.degree → Coef) :
    ∑ P ∈ allowedPatterns s, F P.d.val P.rt.val P.rx.val P.other =
    ∑ d ∈ Finset.Icc 1 D, ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
      (if Q d rt rx ∧ rt + rx ≤ d then
        ∑ m ∈ (Finset.univ : Finset (Pattern s.degree)).filter
          (fun m ↦ patternWeight m = d - rt - rx), F d rt rx m
      else 0) := by sorry
