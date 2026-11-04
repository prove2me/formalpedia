-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControlBudget_bank_le
-- name    : ThreeSum.WeightedGlobalArenaSourceControlBudget.bank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:15:19.927562+00:00
-- url     : https://prove2.me/theorems/f4ad24b7-46f6-46c6-8fff-4984df6e3a01
-- title:
--   Weighted Global Arena Source Control Budget: bank le
-- statement:
--   The Weighted Global Arena Source Control Budget construction uses the bank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L19-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L19-L28

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceControlBudget.bank_le (m r : ℕ) : nb m r≤4^(N m r) := by sorry
