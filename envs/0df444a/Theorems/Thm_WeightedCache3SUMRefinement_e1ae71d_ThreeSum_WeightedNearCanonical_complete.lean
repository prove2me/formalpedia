-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:44:29.519479+00:00
-- url     : https://prove2.me/theorems/6fefffc3-3b6a-451c-83c9-3a71d0709e23
-- title:
--   complete
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L41-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L41-L48

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.complete {N D : ℕ} (Q R : TritWord N) (hR : R∈nearWords Q D) :
    ∃ j<(WeightedNearEnumeration.codes (wordList Q) D).length, word Q D j=R := by sorry
