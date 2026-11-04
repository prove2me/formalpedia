-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentSourceProgram_positions_range
-- name    : ThreeSum.LightWeightedGlobalMomentSourceProgram.positions_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:46:29.547907+00:00
-- url     : https://prove2.me/theorems/9f9dbce6-dabd-4ebf-9652-e3110c6585ef
-- title:
--   Light Weighted Global Moment Source Program: positions range
-- statement:
--   The Light Weighted Global Moment Source Program construction uses the positions range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L55-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L55-L60

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels

theorem ThreeSum.LightWeightedGlobalMomentSourceProgram.positions_range (arity : ℕ) (h : arity=115) :
    ∀ a∈positions, 9≤a ∧ a<arity := by sorry
