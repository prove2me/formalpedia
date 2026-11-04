-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childAt_eq_get
-- name    : ThreeSum.LightBlockChildrenIndexed.childAt_eq_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:34.595316+00:00
-- url     : https://prove2.me/theorems/293e4649-9f7b-4d67-92c5-b538e75dbda6
-- title:
--   Light Block Children Indexed: child At eq get
-- statement:
--   The Light Block Children Indexed construction uses the child At eq get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L85-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L85-L89

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}

theorem ThreeSum.LightBlockChildrenIndexed.childAt_eq_get {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (i : ℕ) (hi : i < groupSize h) :
    childAt q pre hk i = (childPrefixes q pre hk)[i]'(by rw [childPrefixes_length]; exact hi) := by sorry
