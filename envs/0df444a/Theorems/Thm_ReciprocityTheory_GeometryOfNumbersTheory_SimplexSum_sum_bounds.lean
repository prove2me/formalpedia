-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_sum_bounds
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.sum_bounds
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:58.240988+00:00
-- url     : https://prove2.me/theorems/22ec3f49-51f9-4a74-aa2a-83ee83381e24
-- title:
--   Simplex Sum: sum bounds
-- statement:
--   The Simplex Sum construction uses the sum bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L33-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Asymptotics Finset
open ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum

theorem ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.sum_bounds (k n : ℕ) :
    (n : ℝ) ^ (k + 1) ≤ (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ∧
      (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ≤ (n : ℝ) ^ (k + 1) + (k + 1) * (n : ℝ) ^ k := by sorry
