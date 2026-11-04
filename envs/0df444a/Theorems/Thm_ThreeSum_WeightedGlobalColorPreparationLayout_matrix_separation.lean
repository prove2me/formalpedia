-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColorPreparationLayout_matrix_separation
-- name    : ThreeSum.WeightedGlobalColorPreparationLayout.matrix_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:00.418606+00:00
-- url     : https://prove2.me/theorems/d963a93c-b5b3-4738-9c61-e0974d7719f0
-- title:
--   Weighted Global Color Preparation Layout: matrix separation
-- statement:
--   The Weighted Global Color Preparation Layout construction uses the matrix separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L34-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalColorPreparationLayout.matrix_separation (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)=cMatrix free n W nB J ∧
    cMatrix free n W nB J+nC*(J+2)=carry free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)=positions free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J=oMatrix free n W nA nB nC J := by sorry
