-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalExecutable_reporting_length
-- name    : ThreeSum.WeightedGlobalExecutable.reporting_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:02:32.025778+00:00
-- url     : https://prove2.me/theorems/a6cd0b20-243f-4aa7-84b4-84ed8d6f6656
-- title:
--   Weighted Global Executable: reporting length
-- statement:
--   The Weighted Global Executable construction uses the reporting length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutable.lean#L55-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutable.lean#L55-L57

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExecutable
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCanonicalDictionaries
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalExecutable.reporting_length (maps : Fin F→Weight m p) (cap K : ℕ) :
    (reporting maps cap K).length=reportingMain (p := p) K+1 := by sorry
