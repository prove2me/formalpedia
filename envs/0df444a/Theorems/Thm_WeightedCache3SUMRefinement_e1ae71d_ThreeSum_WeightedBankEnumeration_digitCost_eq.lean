-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_digitCost_eq
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.digitCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:23.76751+00:00
-- url     : https://prove2.me/theorems/cf5b4785-5c1f-4fd8-8f8c-ae42e2e709be
-- title:
--   digitCost_eq
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L23-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean#L23-L24

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.digitCost_eq (d : Fin 3) : digitCost d.val = (![0,1369,2740] : Fin 3→ℕ) d := by sorry
