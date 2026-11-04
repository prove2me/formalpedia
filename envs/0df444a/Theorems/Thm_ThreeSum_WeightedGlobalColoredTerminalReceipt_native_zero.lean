-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredTerminalReceipt_native_zero
-- name    : ThreeSum.WeightedGlobalColoredTerminalReceipt.native_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:19:41.703269+00:00
-- url     : https://prove2.me/theorems/432c7f6b-0ace-4d56-bf77-4b498a2d7a5a
-- title:
--   Weighted Global Colored Terminal Receipt: native zero
-- statement:
--   The Weighted Global Colored Terminal Receipt construction uses the native zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean#L52-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean#L52-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedTerminal_native_zero
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSignedSelection_native_zero

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
open WeightedGlobalColoredLoopSetup LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredTerminalReceipt.native_zero (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    WeightedGlobalNativeTensorScore.pairedPotential
      (WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
        (nativeInput P n free menu c A B C initial)) P.K (J P n)
      (WeightedGlobalArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (WeightedGlobalArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))=0 := by sorry
