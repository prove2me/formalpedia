-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_pow_succ_lower
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.pow_succ_lower
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:03.935702+00:00
-- url     : https://prove2.me/theorems/c149484d-d8de-4ad7-97b6-586278d4a4f7
-- title:
--   Simplex Sum: pow succ lower
-- statement:
--   The Simplex Sum construction uses the pow succ lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L9-L20

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.pow_succ_lower (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ (k + 1) + (k + 1) * x ^ k ≤ (x + 1) ^ (k + 1) := by sorry
