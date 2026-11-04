-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaHeaderAgreement_output_cost
-- name    : ThreeSum.WeightedGlobalArenaHeaderAgreement.output_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:00:47.575568+00:00
-- url     : https://prove2.me/theorems/d46419f1-6059-481d-a041-320405561286
-- title:
--   Weighted Global Arena Header Agreement: output cost
-- statement:
--   The Weighted Global Arena Header Agreement construction uses the output cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L47-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L47-L55

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Theorems.Thm_ThreeSum_WeightedSchedule_output_cost

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaHeaderAgreement
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaHeaderAgreement.output_cost (Q : WeightedGlobalGoodOutputCatalog.Output m) (r : ℕ) :
    WeightedGlobalBank.cacheCost (WeightedGlobalRepeatedWords.canonical (fun _ : Fin r=>Q.val))=
      (1024*alphaRank m+3*fixedAlpha m 2)*r := by sorry
