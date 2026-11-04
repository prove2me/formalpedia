-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryLookup_tuple_lookup
-- name    : ThreeSum.WeightedGlobalTupleDictionaryLookup.tuple_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:53:20.675136+00:00
-- url     : https://prove2.me/theorems/08f30b89-899d-45c0-b55a-5efed5fcba19
-- title:
--   Weighted Global Tuple Dictionary Lookup: tuple lookup
-- statement:
--   The Weighted Global Tuple Dictionary Lookup construction uses the tuple lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryLookup.lean#L16-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryLookup.lean#L16-L31

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTupleWitness
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryLookup
open LightTernarySourceHost
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalTupleDictionaryLookup.tuple_lookup {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) :
    ∃ j : ℕ, j<base.length^r ∧ ∀ (raw : A→ℤ) (p : ℕ),
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs := by sorry
