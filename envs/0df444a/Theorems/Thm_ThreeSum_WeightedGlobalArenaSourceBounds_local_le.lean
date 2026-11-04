-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_local_le
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.local_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:03:23.189706+00:00
-- url     : https://prove2.me/theorems/7af6fbe7-a3d8-4483-92a4-e2e8006dda9e
-- title:
--   Weighted Global Arena Source Bounds: local le
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the local le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L66-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L66-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceBounds.local_le (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :
    (localRecords maps cap right).length≤sourceWidth maps cap := by sorry
