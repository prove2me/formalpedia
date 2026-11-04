-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_remaining_succ_cast
-- name    : ThreeSum.WeightedScore.remaining_succ_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:22.035459+00:00
-- url     : https://prove2.me/theorems/e134eddc-0820-4825-a832-a65c2cc5e056
-- title:
--   Weighted Score: remaining succ cast
-- statement:
--   The Weighted Score construction uses the remaining succ cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L101-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L101-L106

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.remaining_succ_cast (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    (remaining primes s q nA nB nC a b c (i+1) : ℤ) =
      (remaining primes s q nA nB nC a b c i : ℤ) -
        (count (joint q (primes i)) nA nB nC a b c : ℤ) := by sorry
