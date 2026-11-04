-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteInputs_selected_abs_le
-- name    : ThreeSum.SourceFiniteInputs.selected_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:17:41.4447+00:00
-- url     : https://prove2.me/theorems/d71ad37e-ef94-4846-aceb-6b6462d33a87
-- title:
--   Source Finite Inputs: selected abs le
-- statement:
--   The Source Finite Inputs construction uses the selected abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L57-L60

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

theorem ThreeSum.SourceFiniteInputs.selected_abs_le (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    |(RawAKeyLists.selected M P xs h J : ℤ)| ≤ (M : ℤ) := by sorry
