-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_S_zero
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.S_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:17.366149+00:00
-- url     : https://prove2.me/theorems/8b349f85-a42a-570f-bb2d-bbfadf9f4e66
-- title:
--   Simplex Sum: S zero
-- statement:
--   The Simplex Sum construction uses the S zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L53-L56

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.S_zero (i n : ℕ) : S i 0 n = ∑ a ∈ range (n + 1), (a : ℝ) ^ i := by sorry
