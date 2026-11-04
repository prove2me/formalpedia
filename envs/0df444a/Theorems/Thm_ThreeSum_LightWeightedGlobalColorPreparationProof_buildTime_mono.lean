-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparationProof_buildTime_mono
-- name    : ThreeSum.LightWeightedGlobalColorPreparationProof.buildTime_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:18:24.734711+00:00
-- url     : https://prove2.me/theorems/9437e67a-c08c-4c33-b7cb-00aad2b0a3a1
-- title:
--   Light Weighted Global Color Preparation Proof: build Time mono
-- statement:
--   The Light Weighted Global Color Preparation Proof construction uses the build Time mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L410-L416
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L410-L416

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalColorPreparationProof.buildTime_mono (n J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    buildTime a b c J U≤buildTime n n n J U := by sorry
