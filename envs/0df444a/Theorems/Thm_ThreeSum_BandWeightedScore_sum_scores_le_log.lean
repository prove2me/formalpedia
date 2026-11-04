-- Prove2me | Theorems.Thm_ThreeSum_BandWeightedScore_sum_scores_le_log
-- name    : ThreeSum.BandWeightedScore.sum_scores_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:30:38.392317+00:00
-- url     : https://prove2.me/theorems/e10669b8-4b3a-42d7-b169-a95278dfa4f0
-- title:
--   Band Weighted Score: sum scores le log
-- statement:
--   The Band Weighted Score construction uses the sum scores le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L135-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L135-L147

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_WeightedCache3SUM_Alias_3f265c13f17dd5ba
import Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le_log

set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

theorem ThreeSum.BandWeightedScore.sum_scores_le_log (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC g A B C rs) ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by sorry
