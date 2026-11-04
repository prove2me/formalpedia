-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_bank_size
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.bank_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:02:02.837206+00:00
-- url     : https://prove2.me/theorems/c7e4fee1-ca56-42ba-9c0e-77612266f6a6
-- title:
--   Weighted Global Arena Source Bounds: bank size
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the bank size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L155-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L155-L163

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceBounds.bank_size (m j : ℕ) : nb m j≤(4^fixedLength m)^j := by sorry
