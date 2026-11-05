-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_read_of_seg
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical.read_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:18:43.738368+00:00
-- url     : https://prove2.me/theorems/86151119-5783-43c8-a61b-bb53645f276c
-- title:
--   read_of_seg
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankCanonical.lean#L60-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankCanonical.lean#L60-L65

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStageModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedBankEnumeration ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical.read_of_seg {N T a : ℕ} (μ : ℕ→ℤ)
    (hseg : Light.Seg μ a ((codes N T).map (fun c => (c : ℤ)))) :
    ∀ j<(codes N T).length, μ (a+j)=(address ((enumeration N T).word j) : ℤ) := by sorry
