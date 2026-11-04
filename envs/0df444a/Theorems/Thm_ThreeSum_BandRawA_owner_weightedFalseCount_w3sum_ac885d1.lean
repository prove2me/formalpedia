-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.owner_weightedFalseCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:56.129861+00:00
-- url     : https://prove2.me/theorems/9e451f68-f2fc-404d-be4e-5a09f3f36b09
-- title:
--   Band Raw A: owner weighted False Count
-- statement:
--   The Band Raw A construction uses the owner weighted False Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L27-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L27-L55

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.owner_weightedFalseCount_w3sum_ac885d1 (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    Arithmetic.weightedFalseCount (ownerProduct nA nB nC g rs s)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.block primes aux q nA nB nC g A B C (rs.getD s default) := by sorry
