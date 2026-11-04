-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankStages_inverse_bound
-- name    : ThreeSum.LightTernaryBankStages.inverse_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:13.175132+00:00
-- url     : https://prove2.me/theorems/210cd83b-9798-4567-a8b9-fcafbade1eb8
-- title:
--   Light Ternary Bank Stages: inverse bound
-- statement:
--   The Light Ternary Bank Stages construction uses the inverse bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L21-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L21-L28

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryBankStages.inverse_bound {N : ℕ} (k : ℕ) (hk : k≤N)
    (H : TritWord N→ℤ) (V : ℕ) (hH : ∀ R, |H R|≤(V : ℤ)) (R : TritWord N) :
    |stageValue k H R|≤((4^N*V : ℕ) : ℤ) := by sorry
