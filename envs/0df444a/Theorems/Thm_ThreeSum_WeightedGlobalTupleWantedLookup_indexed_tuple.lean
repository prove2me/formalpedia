-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleWantedLookup_indexed_tuple
-- name    : ThreeSum.WeightedGlobalTupleWantedLookup.indexed_tuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:02:45.1598+00:00
-- url     : https://prove2.me/theorems/6cbac87e-ef83-4fca-953f-ac92796553e0
-- title:
--   Weighted Global Tuple Wanted Lookup: indexed tuple
-- statement:
--   The Weighted Global Tuple Wanted Lookup construction uses the indexed tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L25-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L25-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalTupleWantedLookup.indexed_tuple {A : Type*} (base : List A) (xs : List A)
    (hx : ∀ x∈xs, x∈base) :
    ∃ is : List ℕ, is.length=xs.length ∧ (∀ i∈is, i<base.length) ∧
      ∀ (B : Type*) (raw : A→B) (fallback : B),
        is.map (fun i => (base.map raw).getD i fallback)=xs.map raw := by sorry
