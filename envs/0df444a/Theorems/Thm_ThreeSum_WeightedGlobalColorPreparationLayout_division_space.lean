-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColorPreparationLayout_division_space
-- name    : ThreeSum.WeightedGlobalColorPreparationLayout.division_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:47.526385+00:00
-- url     : https://prove2.me/theorems/d1d7ec34-1c39-4c73-ac79-30d40c977b83
-- title:
--   Weighted Global Color Preparation Layout: division space
-- statement:
--   The Weighted Global Color Preparation Layout construction uses the division space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L41-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L41-L56

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalColorPreparationLayout.division_space (free n W nA nB nC J U : ℕ) :
    LightTernarySignedMatrix.space (work free n W nA nB nC J) U≤arenaFree free n W nA nB nC J U ∧
    LightTernaryCarryCodes.space (work free n W nA nB nC J) (2^J)≤arenaFree free n W nA nB nC J U := by sorry
