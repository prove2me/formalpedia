-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_query_bound
-- name    : ThreeSum.WeightedGlobalColoredRuntimeCertificate.query_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T03:27:28.89142+00:00
-- url     : https://prove2.me/theorems/11e021ba-7510-48d1-89c6-dd62f9725315
-- title:
--   Weighted Global Colored Runtime Certificate: query bound
-- statement:
--   The separately priced global query maximum is charged exactly once.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean#L80-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean#L80-L87

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

theorem ThreeSum.WeightedGlobalColoredRuntimeCertificate.query_bound (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hn : 1<n) :
    (WeightedGlobalActualGlobalQueryRuntime.queryCap (state P n free menu c A B C initial) n:ℝ)≤
      (WeightedGlobalUniformQueryTime.coefficient P.m P.wordD P.allocation.E κ:ℝ)*
        ((state P n free menu c A B C initial).arena.J+1:ℕ)^3*
          WeightedGlobalCountFrontendBudget.envelope P.m (WeightedGlobalCoverScale.radixLength P.m n) := by sorry
