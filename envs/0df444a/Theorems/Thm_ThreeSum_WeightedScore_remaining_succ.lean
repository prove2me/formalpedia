-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_remaining_succ
-- name    : ThreeSum.WeightedScore.remaining_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:17.700082+00:00
-- url     : https://prove2.me/theorems/b620fcca-d621-4457-b2ec-0a6464c66ef2
-- title:
--   Weighted Score: remaining succ
-- statement:
--   The Weighted Score construction uses the remaining succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L93-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L93-L99

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.remaining_succ (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c (i+1) =
      remaining primes s q nA nB nC a b c i -
        count (joint q (primes i)) nA nB nC a b c := by sorry
