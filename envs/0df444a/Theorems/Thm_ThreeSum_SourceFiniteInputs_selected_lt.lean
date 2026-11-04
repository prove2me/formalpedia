-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteInputs_selected_lt
-- name    : ThreeSum.SourceFiniteInputs.selected_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:18:14.522207+00:00
-- url     : https://prove2.me/theorems/3f70b7d3-69ee-4eed-a8aa-9fcc12cb2ed9
-- title:
--   Source Finite Inputs: selected lt
-- statement:
--   The Source Finite Inputs construction uses the selected lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L52-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L52-L55

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_lt
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt
import Theorems.Thm_ThreeSum_RawAKeyLists_selected_lt

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

theorem ThreeSum.SourceFiniteInputs.selected_lt (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    RawAKeyLists.selected M P xs h J < M := by sorry
