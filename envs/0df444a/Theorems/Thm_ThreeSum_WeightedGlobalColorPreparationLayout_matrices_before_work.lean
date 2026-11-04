-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColorPreparationLayout_matrices_before_work
-- name    : ThreeSum.WeightedGlobalColorPreparationLayout.matrices_before_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:50.642012+00:00
-- url     : https://prove2.me/theorems/58455b64-6d49-4724-8d10-51c9d8d20b7e
-- title:
--   Weighted Global Color Preparation Layout: matrices before work
-- statement:
--   The Weighted Global Color Preparation Layout construction uses the matrices before work property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L25-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L25-L32

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalColorPreparationLayout.matrices_before_work (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)≤work free n W nA nB nC J ∧
    cMatrix free n W nB J+nC*(J+2)≤work free n W nA nB nC J ∧
    oMatrix free n W nA nB nC J+nA*2^J*(J+2)≤work free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J≤work free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)≤work free n W nA nB nC J := by sorry
