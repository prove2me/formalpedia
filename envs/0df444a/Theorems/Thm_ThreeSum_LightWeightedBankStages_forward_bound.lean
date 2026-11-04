-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankStages_forward_bound
-- name    : ThreeSum.LightWeightedBankStages.forward_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:41.028751+00:00
-- url     : https://prove2.me/theorems/1deb8c39-7157-4620-ac82-a8ac6592cb24
-- title:
--   Light Weighted Bank Stages: forward bound
-- statement:
--   The Light Weighted Bank Stages construction uses the forward bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean#L17-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean#L17-L24

import Definitions.Def_Submission_Weighted_BankSweep
import Definitions.Def_Submission_Weighted_BankStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedBankStages.forward_bound {N : ℕ} (k : ℕ) (hk : k≤N)
    (F : TritWord N→ℤ) (V : ℕ) (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage k F R|≤((4^N*V : ℕ) : ℤ) := by sorry
