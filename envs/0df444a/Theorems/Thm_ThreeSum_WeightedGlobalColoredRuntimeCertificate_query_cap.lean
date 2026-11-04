-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_query_cap
-- name    : ThreeSum.WeightedGlobalColoredRuntimeCertificate.query_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T03:28:30.392665+00:00
-- url     : https://prove2.me/theorems/9e8b61b9-9777-4377-847f-e4056d0a6d2e
-- title:
--   Weighted Global Colored Runtime Certificate: query cap
-- statement:
--   The Weighted Global Colored Runtime Certificate construction uses the query cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean#L75-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean#L75-L77

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredRuntimeCertificate.query_cap : WeightedGlobalActualGlobalQueryRuntime.queryCap (state P n free menu c A B C initial) n≤
    queryTime P n free A B C := by sorry
