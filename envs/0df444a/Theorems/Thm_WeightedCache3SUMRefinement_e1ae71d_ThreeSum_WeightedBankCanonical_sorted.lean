-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_sorted
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical.sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:18:22.139695+00:00
-- url     : https://prove2.me/theorems/caa2c86e-ad32-487e-b58f-9159980f58e8
-- title:
--   sorted
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankCanonical.lean#L51-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankCanonical.lean#L51-L56

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical.sorted (N T : ℕ) : ∀ j k, j<k → k<(codes N T).length →
    address ((enumeration N T).word j)<address ((enumeration N T).word k) := by sorry
