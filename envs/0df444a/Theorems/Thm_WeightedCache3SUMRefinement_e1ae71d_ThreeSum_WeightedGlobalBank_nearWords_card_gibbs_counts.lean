-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_nearWords_card_gibbs_counts
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.nearWords_card_gibbs_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:12.475485+00:00
-- url     : https://prove2.me/theorems/70fc3422-e68a-4b9a-b23b-5662c4706eac
-- title:
--   nearWords_card_gibbs_counts
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean#L33-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean#L33-L38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs_counts

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.nearWords_card_gibbs_counts {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (nearWords Q D).card*z^D≤(1+z^1369)^digitCount Q 1*(1+z^1371+z^2740)^digitCount Q 2 := by sorry
