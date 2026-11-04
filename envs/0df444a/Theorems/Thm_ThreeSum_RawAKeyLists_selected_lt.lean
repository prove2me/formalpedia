-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_selected_lt
-- name    : ThreeSum.RawAKeyLists.selected_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:17.109387+00:00
-- url     : https://prove2.me/theorems/6e2990ea-d35b-4f99-bb66-e5f75e36cbcc
-- title:
--   Raw AKey Lists: selected lt
-- statement:
--   The Raw AKey Lists construction uses the selected lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L111-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L111-L112

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_lt
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt

set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.selected_lt (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    selected M P xs h J < M := by sorry
