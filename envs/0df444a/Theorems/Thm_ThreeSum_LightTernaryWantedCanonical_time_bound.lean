-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_time_bound
-- name    : ThreeSum.LightTernaryWantedCanonical.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:47.675568+00:00
-- url     : https://prove2.me/theorems/0f8a7770-d5c8-463e-8a4a-d69afe409f34
-- title:
--   Light Ternary Wanted Canonical: time bound
-- statement:
--   The Light Ternary Wanted Canonical construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L52-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L52-L71

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_child_target_bound
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedRadix_localBucket_eq_of_emod
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_length_le
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedCanonical
open Light
open TernaryWantedRadix (localBucket mem_localBucket localBucket_eq_of_emod wantedOutputs wantedOutputs_length_le child_target_bound codeLimit codeLimit_base codeLimit_child)
open TernaryWantedLittleEndian (wantedCodes wantedCodes_length wantedCodes_succ encode)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

theorem ThreeSum.LightTernaryWantedCanonical.time_bound (P C V : ℕ) (hC : 1 ≤ C) : ∀ j,
    time P C V j ≤ (overhead P V+stepCost V+40)*(j+1)*C^j := by sorry
