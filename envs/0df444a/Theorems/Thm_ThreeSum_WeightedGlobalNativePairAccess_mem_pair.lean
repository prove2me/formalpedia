-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
-- name    : ThreeSum.WeightedGlobalNativePairAccess.mem_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:16:50.025823+00:00
-- url     : https://prove2.me/theorems/4d9e2dfe-dc83-45d7-83f0-0d977cbecdfc
-- title:
--   Weighted Global Native Pair Access: mem pair
-- statement:
--   The Weighted Global Native Pair Access construction uses the mem pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairAccess.lean#L16-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairAccess.lean#L16-L25

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalNativePairAccess.mem_pair {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (i b c j k : ℕ) : ((b,j),(c,k))∈pairs S i ↔
      (b,j)∈S.left.records ∧ S.left.group j=S.front.group i ∧
      (c,k)∈S.right.records ∧ S.right.group k=S.front.group i ∧
      TernaryConvolution.Adds (S.front.E.word (S.left.key j))
        (S.front.E.word (S.right.key k)) (S.front.Q i) := by sorry
