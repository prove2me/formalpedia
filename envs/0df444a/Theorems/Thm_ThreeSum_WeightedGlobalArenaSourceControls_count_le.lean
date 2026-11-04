-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControls_count_le
-- name    : ThreeSum.WeightedGlobalArenaSourceControls.count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:06:40.043268+00:00
-- url     : https://prove2.me/theorems/86c1cf93-6117-4f86-8644-89fe1b399f13
-- title:
--   Weighted Global Arena Source Controls: count le
-- statement:
--   The Weighted Global Arena Source Controls construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControls.lean#L23-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControls.lean#L23-L34

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_TernaryWantedBatchCount_count_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceControls
open Light WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps LightTernarySourceHost
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceControls.count_le (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) :
    count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input≤
      rowBound (r := r) maps cap I right := by sorry
