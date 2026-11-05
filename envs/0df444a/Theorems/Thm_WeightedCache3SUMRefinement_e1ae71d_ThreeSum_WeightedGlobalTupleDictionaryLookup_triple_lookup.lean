-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryLookup_triple_lookup
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup.triple_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:35:41.296508+00:00
-- url     : https://prove2.me/theorems/4e186dd0-767e-4788-b5ac-6f2bcee2cffa
-- title:
--   triple_lookup
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleDictionaryLookup.lean#L35-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleDictionaryLookup.lean#L35-L42

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTupleWitness
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup
open LightTernarySourceHost
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup.triple_lookup {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) (raw word group : A→ℤ) (p R F : ℕ) :
    ∃ j : ℕ, j<base.length^r ∧
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs ∧
      dictionary (base.map word) R r j=Radix.positionalHash (R : ℤ) word xs ∧
      dictionary (base.map group) F r j=Radix.positionalHash (F : ℤ) group xs := by sorry
