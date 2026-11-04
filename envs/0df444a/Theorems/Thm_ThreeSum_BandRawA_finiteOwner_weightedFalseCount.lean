-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteOwner_weightedFalseCount
-- name    : ThreeSum.BandRawA.finiteOwner_weightedFalseCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:40.207134+00:00
-- url     : https://prove2.me/theorems/b065e464-917b-483a-b203-8d7d7dfaab7b
-- title:
--   Band Raw A: finite Owner weighted False Count
-- statement:
--   The Band Raw A construction uses the finite Owner weighted False Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L128-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L128-L139

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finiteOwner_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    Arithmetic.weightedFalseCount (finiteOwnerProduct nA nB nC g rs s)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.block primes aux q nA nB nC g A B C (rs.getD s default) := by sorry
