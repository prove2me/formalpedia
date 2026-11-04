-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankStages_inverse_bound
-- name    : ThreeSum.LightWeightedBankStages.inverse_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:24.87559+00:00
-- url     : https://prove2.me/theorems/b2d99d16-ebca-4da0-97e0-303463f0381b
-- title:
--   Light Weighted Bank Stages: inverse bound
-- statement:
--   The Light Weighted Bank Stages construction uses the inverse bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean#L26-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean#L26-L33

import Definitions.Def_Submission_Weighted_BankSweep
import Definitions.Def_Submission_Weighted_BankStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedBankStages.inverse_bound {N : ℕ} (k : ℕ) (hk : k≤N)
    (H : TritWord N→ℤ) (V : ℕ) (hH : ∀ R, |H R|≤(V : ℤ)) (R : TritWord N) :
    |stageValue k H R|≤((4^N*V : ℕ) : ℤ) := by sorry
