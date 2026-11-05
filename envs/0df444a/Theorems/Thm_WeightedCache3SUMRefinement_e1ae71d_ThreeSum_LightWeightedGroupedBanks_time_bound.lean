-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupedBanks_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:19:26.150604+00:00
-- url     : https://prove2.me/theorems/d859b81b-4e2e-44ad-ac3a-3b89d6e28cac
-- title:
--   time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GroupBankResources.lean#L20-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GroupBankResources.lean#L20-L27

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupedBanks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankCoordinate_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankSweep_time_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks.time_bound (groups N L n : ℕ) :
    time groups N L n≤31000*(groups+1)*(N+1)*(N+L+1)*(n+1) := by sorry
