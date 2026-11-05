-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_visits_cons_all
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost.visits_cons_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:24.557505+00:00
-- url     : https://prove2.me/theorems/1bfb264c-79b5-4d4d-9f0a-823c65066f8a
-- title:
--   visits_cons_all
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenQueryCost.lean#L69-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenQueryCost.lean#L69-L77

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_cons_all

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost.visits_cons_all (q : Fin 3) (qs : List ℕ) (D : ℕ) (hD : 2740≤D) :
    WeightedNearEnumeration.visits (q.val::qs) D =
      1 + ∑ d : Fin 3, if d≤q then
        WeightedNearEnumeration.visits qs (D-(digitCost q.val-digitCost d.val)) else 0 := by sorry
