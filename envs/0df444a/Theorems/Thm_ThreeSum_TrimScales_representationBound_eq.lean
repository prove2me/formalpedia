-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_representationBound_eq
-- name    : ThreeSum.TrimScales.representationBound_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:18.681811+00:00
-- url     : https://prove2.me/theorems/d4c87b76-db19-4839-b0f7-36ca43861070
-- title:
--   Trim Scales: representation Bound eq
-- statement:
--   The Trim Scales construction uses the representation Bound eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L229-L231
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L229-L231

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.representationBound_eq (n : ℕ) :
    representationBound n = scheduleCount n * trimMultiplicity n := by sorry
