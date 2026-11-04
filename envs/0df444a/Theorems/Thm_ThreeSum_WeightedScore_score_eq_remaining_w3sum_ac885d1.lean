-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_score_eq_remaining_w3sum_ac885d1
-- name    : ThreeSum.WeightedScore.score_eq_remaining_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:24.285777+00:00
-- url     : https://prove2.me/theorems/4dbefe72-e197-4b55-ad34-8dd3547bcce8
-- title:
--   Weighted Score: score eq remaining
-- statement:
--   The Weighted Score construction uses the score eq remaining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L108-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L108-L132

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.score_eq_remaining_w3sum_ac885d1 (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) :
    score primes s q nA nB nC a b c = remaining primes s q nA nB nC a b c s := by sorry
