-- Prove2me | Theorems.Thm_ThreeSum_LightGuardedWanted_selected_eq
-- name    : ThreeSum.LightGuardedWanted.selected_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:21.095504+00:00
-- url     : https://prove2.me/theorems/a9ba904a-6aa9-4373-90ff-89ad36b22c8c
-- title:
--   Light Guarded Wanted: selected eq
-- statement:
--   The Light Guarded Wanted construction uses the selected eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L61-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L61-L66

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

theorem ThreeSum.LightGuardedWanted.selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by sorry
