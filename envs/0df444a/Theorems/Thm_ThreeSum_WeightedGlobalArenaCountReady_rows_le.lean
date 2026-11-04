-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_rows_le
-- name    : ThreeSum.WeightedGlobalArenaCountReady.rows_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:42:59.26986+00:00
-- url     : https://prove2.me/theorems/0dc0bd3b-4b7f-400a-9919-d85db70886c0
-- title:
--   Weighted Global Arena Count Ready: rows le
-- statement:
--   The Weighted Global Arena Count Ready construction uses the rows le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCountReady.lean#L60-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCountReady.lean#L60-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaCountReady.rows_le (Q : TritWord (N m r)) :
    LightWeightedPreparedWanted.rows Q (cut m r)≤3^(N m r) := by sorry
