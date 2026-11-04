-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_visits_cons
-- name    : ThreeSum.LightTernaryNearEnumeration.visits_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:21.579267+00:00
-- url     : https://prove2.me/theorems/56aee0e5-a437-48bd-9304-256061c0bbaf
-- title:
--   Light Ternary Near Enumeration: visits cons
-- statement:
--   The Light Ternary Near Enumeration construction uses the visits cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L72-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L72-L87

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryNearEnumeration.visits_cons (q : Fin 3) (qs : List ℕ) (D : ℕ) :
    visits (q.val :: qs) D = 1 + branchVisits qs D q.val 0 +
      branchVisits qs D q.val 1 + branchVisits qs D q.val 2 := by sorry
