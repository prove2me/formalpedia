-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childAt_valid
-- name    : ThreeSum.LightBlockChildrenIndexed.childAt_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:19.55422+00:00
-- url     : https://prove2.me/theorems/a95d1c54-b803-47a0-a737-a60b0ba885af
-- title:
--   Light Block Children Indexed: child At valid
-- statement:
--   The Light Block Children Indexed construction uses the child At valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L91-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L91-L95

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}

theorem ThreeSum.LightBlockChildrenIndexed.childAt_valid {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (i : ℕ) (hi : i < groupSize h) : ValidPrefix q (k+1) (childAt q pre hk i) := by sorry
