-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_time_le
-- name    : ThreeSum.WeightedGlobalColoredRuntimeCertificate.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T03:27:37.993253+00:00
-- url     : https://prove2.me/theorems/747e7097-4cd0-4326-9c4b-457c6d5aa75a
-- title:
--   Weighted Global Colored Runtime Certificate: time le
-- statement:
--   The complete concrete runtime ledger is bounded by the size-only
--   per-color time used in the final theorem. No Fits or time premise remains.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean#L91-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeCertificate.lean#L91-L100

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Theorems.Thm_Light_Compiler_Holds_output
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_time_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
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

theorem ThreeSum.WeightedGlobalColoredRuntimeCertificate.time_le (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    WeightedGlobalActualColoredRuntime.time (k:=P.k) P.maps P.output
      (state P n free menu c A B C initial) P.allocation.E κ P.H n≤P.colorTime n := by sorry
