-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_next_count_le_remaining
-- name    : ThreeSum.WeightedScore.next_count_le_remaining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:15.180699+00:00
-- url     : https://prove2.me/theorems/cf601cb8-0f6c-4854-90a9-13743023428a
-- title:
--   Weighted Score: next count le remaining
-- statement:
--   The Weighted Score construction uses the next count le remaining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L83-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L83-L91

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.next_count_le_remaining (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    count (joint q (primes i)) nA nB nC a b c ≤
      remaining primes s q nA nB nC a b c i := by sorry
