-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankStages_forward_bound
-- name    : ThreeSum.LightTernaryBankStages.forward_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:28.419521+00:00
-- url     : https://prove2.me/theorems/fee1a557-9985-4718-9892-e5170626c8da
-- title:
--   Light Ternary Bank Stages: forward bound
-- statement:
--   The Light Ternary Bank Stages construction uses the forward bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L12-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L12-L19

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryBankStages.forward_bound {N : ℕ} (k : ℕ) (hk : k≤N)
    (F : TritWord N→ℤ) (V : ℕ) (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage k F R|≤((4^N*V : ℕ) : ℤ) := by sorry
