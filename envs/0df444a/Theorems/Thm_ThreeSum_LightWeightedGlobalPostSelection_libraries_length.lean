-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_libraries_length
-- name    : ThreeSum.LightWeightedGlobalPostSelection.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:15:30.900115+00:00
-- url     : https://prove2.me/theorems/df856d3d-175d-44ca-a5d0-9862942b5f51
-- title:
--   Light Weighted Global Post Selection: libraries length
-- statement:
--   The Light Weighted Global Post Selection construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L42-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L42-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length


set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open ThreeSum ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule

theorem ThreeSum.LightWeightedGlobalPostSelection.libraries_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    (libraries S H).length = 139*(channels (2*H+1)).length+17 := by sorry
