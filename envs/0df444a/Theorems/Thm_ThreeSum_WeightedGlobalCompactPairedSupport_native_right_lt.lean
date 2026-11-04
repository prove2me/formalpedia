-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_native_right_lt
-- name    : ThreeSum.WeightedGlobalCompactPairedSupport.native_right_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:08:27.59664+00:00
-- url     : https://prove2.me/theorems/3e75d653-e0ca-499b-a1b0-72cd95d42ba2
-- title:
--   Weighted Global Compact Paired Support: native right lt
-- statement:
--   The Weighted Global Compact Paired Support construction uses the native right lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L97-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L97-L103

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalCompactPairedSupport.native_right_lt {N : ℕ} {S : WeightedSourceCountExecutionFactory.Setup N} {i : ℕ}
    (p : WeightedGlobalNativePairMoments.Pair S i) : p.val.2.1 < S.right.NL := by sorry
