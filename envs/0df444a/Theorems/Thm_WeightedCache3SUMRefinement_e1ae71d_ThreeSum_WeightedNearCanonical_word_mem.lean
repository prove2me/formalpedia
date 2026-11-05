-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_word_mem
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.word_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:43:36.165197+00:00
-- url     : https://prove2.me/theorems/ae61f149-2b32-465a-ae85-b5489fbbbd7a
-- title:
--   word_mem
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L34-L39

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.word_mem {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.words (wordList Q) D).length) :
    word Q D j∈nearWords Q D := by sorry
