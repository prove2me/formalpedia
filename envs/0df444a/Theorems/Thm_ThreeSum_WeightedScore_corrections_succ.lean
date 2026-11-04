-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_corrections_succ
-- name    : ThreeSum.WeightedScore.corrections_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:13.531692+00:00
-- url     : https://prove2.me/theorems/21d08e49-6a4f-43e5-8539-cfec4bfd8108
-- title:
--   Weighted Score: corrections succ
-- statement:
--   The Weighted Score construction uses the corrections succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L57-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L57-L62

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.corrections_succ (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    corrections primes q nA nB nC a b c (i+1) =
      corrections primes q nA nB nC a b c i +
        count (joint q (primes i)) nA nB nC a b c := by sorry
