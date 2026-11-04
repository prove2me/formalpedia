-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_visits_cons_all
-- name    : ThreeSum.WeightedFrozenQueryCost.visits_cons_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:15:22.18982+00:00
-- url     : https://prove2.me/theorems/6a3b60a7-19e3-4efb-902d-4e280686a93c
-- title:
--   Weighted Frozen Query Cost: visits cons all
-- statement:
--   The Weighted Frozen Query Cost construction uses the visits cons all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L69-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L69-L77

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_cons_all

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.visits_cons_all (q : Fin 3) (qs : List ℕ) (D : ℕ) (hD : 1025≤D) :
    WeightedNearEnumeration.visits (q.val::qs) D =
      1 + ∑ d : Fin 3, if d≤q then
        WeightedNearEnumeration.visits qs (D-(digitCost q.val-digitCost d.val)) else 0 := by sorry
