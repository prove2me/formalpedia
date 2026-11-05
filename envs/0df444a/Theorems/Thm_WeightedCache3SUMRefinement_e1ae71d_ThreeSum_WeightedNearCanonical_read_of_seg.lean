-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_read_of_seg
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.read_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:44:14.790095+00:00
-- url     : https://prove2.me/theorems/3e097d7c-b5c7-42ef-ad6d-56bc92cd4952
-- title:
--   read_of_seg
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L68-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L68-L74

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_read_of_seg

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.read_of_seg {N D a : ℕ} (Q : TritWord N) (μ : ℕ → ℤ)
    (hseg : Light.Seg μ a ((WeightedNearEnumeration.codes (wordList Q) D).map (fun c => (c : ℤ)))) :
    ∀ j<(WeightedNearEnumeration.codes (wordList Q) D).length,
      μ (a+j)=(address (word Q D j) : ℤ) := by sorry
