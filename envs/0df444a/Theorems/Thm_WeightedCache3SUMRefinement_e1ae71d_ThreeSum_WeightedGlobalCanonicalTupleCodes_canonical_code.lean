-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalTupleCodes_canonical_code
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalTupleCodes.canonical_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:39:44.745502+00:00
-- url     : https://prove2.me/theorems/df0a87a1-1fb4-4ac9-9d7d-167f3e030991
-- title:
--   canonical_code
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L28-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L28-L36

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleWantedLookup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalTupleCodes.canonical_code {A : Type*} {L r : ℕ} (word : A→TritWord L) (xs : Fin r→A) :
    Radix.positionalHash ((4^L : ℕ) : ℤ)
      (fun a => (TernaryCodeSemantics.address (word a) : ℤ)) (List.ofFn xs)=
      (TernaryCodeSemantics.address (WeightedGlobalRepeatedWords.canonical (word ∘ xs)) : ℤ) := by sorry
