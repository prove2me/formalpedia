-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparationProof_arenaFree_mono
-- name    : ThreeSum.LightWeightedGlobalColorPreparationProof.arenaFree_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:14:19.357328+00:00
-- url     : https://prove2.me/theorems/e9643d3e-cbc0-4777-b7e3-20fe843c5def
-- title:
--   Light Weighted Global Color Preparation Proof: arena Free mono
-- statement:
--   The Light Weighted Global Color Preparation Proof construction uses the arena Free mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L401-L408
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L401-L408

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalColorPreparationProof.arenaFree_mono (free n W J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    arenaFree free n W a b c J U≤arenaFree free n W n n n J U := by sorry
