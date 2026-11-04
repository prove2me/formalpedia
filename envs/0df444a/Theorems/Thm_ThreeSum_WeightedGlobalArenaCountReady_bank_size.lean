-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_bank_size
-- name    : ThreeSum.WeightedGlobalArenaCountReady.bank_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:44:19.326648+00:00
-- url     : https://prove2.me/theorems/a85b94dd-5c29-43cc-a002-150c96b1afbd
-- title:
--   Weighted Global Arena Count Ready: bank size
-- statement:
--   The Weighted Global Arena Count Ready construction uses the bank size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCountReady.lean#L48-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCountReady.lean#L48-L51

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
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

theorem ThreeSum.WeightedGlobalArenaCountReady.bank_size (hN : 0<N m r) : nb m r<2^(2*N m r) := by sorry
