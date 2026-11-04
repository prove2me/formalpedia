-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_cons_all
-- name    : ThreeSum.TernaryFrozenQueryCost.visits_cons_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:04.929013+00:00
-- url     : https://prove2.me/theorems/d3598a39-d402-46d5-8252-7cc58396a458
-- title:
--   Ternary Frozen Query Cost: visits cons all
-- statement:
--   The Ternary Frozen Query Cost construction uses the visits cons all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L47-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L47-L53

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.visits_cons_all (q : Fin 3) (qs : List ℕ) (D : ℕ) (hD : 2≤D) :
    TernaryNearEnumeration.visits (q.val::qs) D=
      1+∑ d : Fin 3, if d≤q then
        TernaryNearEnumeration.visits qs (D-(q.val-d.val)) else 0 := by sorry
