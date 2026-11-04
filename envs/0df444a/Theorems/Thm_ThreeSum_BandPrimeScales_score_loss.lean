-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeScales_score_loss
-- name    : ThreeSum.BandPrimeScales.score_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:43.721195+00:00
-- url     : https://prove2.me/theorems/49faacb0-2fa2-4304-9b01-e2b7d652547e
-- title:
--   Band Prime Scales: score loss
-- statement:
--   The Band Prime Scales construction uses the score loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeScales.lean#L88-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeScales.lean#L88-L100

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

theorem ThreeSum.BandPrimeScales.score_loss {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    modulus n nA nB nC A B C rs*score n (modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      scoreLoss k n*score n 1 nA nB nC A B C rs := by sorry
