-- Prove2me | Theorems.Thm_ThreeSum_BandWeightedScore_sum_blocks_le_log
-- name    : ThreeSum.BandWeightedScore.sum_blocks_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:11.253736+00:00
-- url     : https://prove2.me/theorems/332c3411-6cdf-4155-aeb4-ff21fe48c929
-- title:
--   Band Weighted Score: sum blocks le log
-- statement:
--   The Band Weighted Score construction uses the sum blocks le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L118-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L118-L133

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

theorem ThreeSum.BandWeightedScore.sum_blocks_le_log (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (r : Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, block primes s (q*primes i) nA nB nC g A B C r) ≤
      Nat.log y (3*U)*block primes s q nA nB nC g A B C r := by sorry
