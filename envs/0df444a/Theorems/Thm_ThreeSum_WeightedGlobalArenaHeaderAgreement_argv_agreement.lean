-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaHeaderAgreement_argv_agreement
-- name    : ThreeSum.WeightedGlobalArenaHeaderAgreement.argv_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:59:23.668278+00:00
-- url     : https://prove2.me/theorems/36d75f70-343e-4567-94e1-ed59b48e53ec
-- title:
--   Weighted Global Arena Header Agreement: argv agreement
-- statement:
--   After the actual wanted-row loop stores its returned count in header104,
--   the 106 physical words are exactly the concrete host constructor's arguments.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L68-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L68-L92

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaHeaderAgreement
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaHeaderAgreement.argv_agreement (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap j : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (ret : ℤ) :
    (emittedHeader I p m F j Q ret).set 104 ((entries (r:=j+1) maps τ I).length:ℤ)=
      (setup (r:=j+1) maps τ cap Q I).argv := by sorry
