-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_native_left_lt
-- name    : ThreeSum.WeightedGlobalCompactPairedSupport.native_left_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:07:25.16088+00:00
-- url     : https://prove2.me/theorems/871d0131-8cb3-4912-9092-666d1be00c2d
-- title:
--   Weighted Global Compact Paired Support: native left lt
-- statement:
--   The Weighted Global Compact Paired Support construction uses the native left lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L89-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean#L89-L95

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

theorem ThreeSum.WeightedGlobalCompactPairedSupport.native_left_lt {N : ℕ} {S : WeightedSourceCountExecutionFactory.Setup N} {i : ℕ}
    (p : WeightedGlobalNativePairMoments.Pair S i) : p.val.1.1 < S.left.NL := by sorry
