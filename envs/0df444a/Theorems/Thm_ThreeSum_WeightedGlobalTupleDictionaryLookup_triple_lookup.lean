-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryLookup_triple_lookup
-- name    : ThreeSum.WeightedGlobalTupleDictionaryLookup.triple_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:50:18.367141+00:00
-- url     : https://prove2.me/theorems/97cab0e7-327f-4159-9fb7-6120195652b1
-- title:
--   Weighted Global Tuple Dictionary Lookup: triple lookup
-- statement:
--   All three independently generated dictionaries use the same actual tuple
--   index, including collisions of the native integer keys.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryLookup.lean#L35-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryLookup.lean#L35-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTupleWitness
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryLookup
open LightTernarySourceHost
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalTupleDictionaryLookup.triple_lookup {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) (raw word group : A→ℤ) (p R F : ℕ) :
    ∃ j : ℕ, j<base.length^r ∧
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs ∧
      dictionary (base.map word) R r j=Radix.positionalHash (R : ℤ) word xs ∧
      dictionary (base.map group) F r j=Radix.positionalHash (F : ℤ) group xs := by sorry
