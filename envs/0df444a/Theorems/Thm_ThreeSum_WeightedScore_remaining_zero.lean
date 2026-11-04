-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
-- name    : ThreeSum.WeightedScore.remaining_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:22.325625+00:00
-- url     : https://prove2.me/theorems/a35ed6e2-035b-42f5-9a6a-5a4c7fca78bc
-- title:
--   Weighted Score: remaining zero
-- statement:
--   The Weighted Score construction uses the remaining zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L73-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L73-L76

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.remaining_zero (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) :
    remaining primes s q nA nB nC a b c 0 = s * count q nA nB nC a b c := by sorry
