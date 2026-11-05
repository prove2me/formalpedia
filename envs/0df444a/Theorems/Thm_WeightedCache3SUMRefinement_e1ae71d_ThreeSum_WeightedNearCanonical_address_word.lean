-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_address_word
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.address_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:44:39.072845+00:00
-- url     : https://prove2.me/theorems/8654cb6a-a85d-445c-a9f1-455eaa034670
-- title:
--   address_word
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L50-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L50-L58

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_address_word

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.address_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.codes (wordList Q) D).length) :
    address (word Q D j)=(WeightedNearEnumeration.codes (wordList Q) D)[j] := by sorry
