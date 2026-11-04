-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixRuntimeIdentity_init_time
-- name    : ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.init_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:15:51.125023+00:00
-- url     : https://prove2.me/theorems/e620fa96-9e95-4c62-b11e-fd8dc04b638c
-- title:
--   Weighted Global Colored Prefix Runtime Identity: init time
-- statement:
--   The physical finite-sup loop budget is exactly the all-prefix budget
--   used by the size-only runtime analysis.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean#L79-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean#L79-L97

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLoop
open LightWeightedGlobalSeedScoreFactory WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
open WeightedGlobalActualSeedRuntime
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.init_time (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    (post : Input) (cleanup : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) :
    (setup P n free menu c A B C μ).initTime=
      allPrefixTime (k:=P.k) P.maps P.output
        (runtimeState P n free menu c A B C μ post cleanup keysB keysC).phase
        (runtimeState P n free menu c A B C μ post cleanup keysB keysC).arena
        (runtimeState P n free menu c A B C μ post cleanup keysB keysC).seeds n := by sorry
