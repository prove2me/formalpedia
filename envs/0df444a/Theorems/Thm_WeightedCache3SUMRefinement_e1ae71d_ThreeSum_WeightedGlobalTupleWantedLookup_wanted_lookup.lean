-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleWantedLookup_wanted_lookup
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleWantedLookup.wanted_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:39:09.125784+00:00
-- url     : https://prove2.me/theorems/c1e2e075-19c9-45a2-aee9-bc9ab5cc7fe5
-- title:
--   wanted_lookup
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L49-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L49-L71

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleWantedLookup.wanted_lookup {A : Type*} (base xs : List A) (r : ℕ)
    (hx : xs∈RadixKeyLists.tuples base r) (p : ℕ) (hp : p≠0)
    (raw : A→ℤ) (word group : A→ℕ) (R F : ℕ) (x : ℤ)
    (hdiv : (p : ℤ)^r∣x-Radix.positionalHash (p : ℤ) raw xs) :
    (Nat.ofDigits R (xs.map word),Nat.ofDigits F (xs.map group))∈
      wantedCodes (p : ℤ) (base.map raw) (base.map word) (base.map group) r x R F 0 1 0 1 := by sorry
