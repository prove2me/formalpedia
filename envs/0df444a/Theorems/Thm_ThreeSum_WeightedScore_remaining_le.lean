-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_remaining_le
-- name    : ThreeSum.WeightedScore.remaining_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:10.597569+00:00
-- url     : https://prove2.me/theorems/cd4ef5fd-965a-4f88-9a64-2a892766eb31
-- title:
--   Weighted Score: remaining le
-- statement:
--   The Weighted Score construction uses the remaining le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L78-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L78-L81

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.remaining_le (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c i ≤ s * (nA*nB*nC) := by sorry
