-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.codes_length_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:24.750611+00:00
-- url     : https://prove2.me/theorems/640e3a58-4001-49d9-9092-820aa55cf42d
-- title:
--   codes_length_gibbs
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L92-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L92-L96

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.codes_length_gibbs (N T : ℕ) (y : ℝ) (hy : 0≤y) (hy1 : y≤1) :
    (codes N T).length*y^T ≤ (1+y^1369+y^2740)^N := by sorry
