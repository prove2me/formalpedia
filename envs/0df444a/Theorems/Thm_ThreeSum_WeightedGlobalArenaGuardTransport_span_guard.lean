-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaGuardTransport_span_guard
-- name    : ThreeSum.WeightedGlobalArenaGuardTransport.span_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:33:34.298699+00:00
-- url     : https://prove2.me/theorems/25d4b012-c880-4262-a6f2-7a7455180189
-- title:
--   Weighted Global Arena Guard Transport: span guard
-- statement:
--   Replaying a selected actual candidate needs only the same immutable
--   input invariant. The real span extension reads catalog7 and writes8.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaGuardTransport.lean#L197-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaGuardTransport.lean#L197-L237

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaGuardTransport.span_guard {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : WeightedGlobalArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : WeightedGlobalArenaCandidateGuard.Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (h : KeepInputs I μ ν) (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hτ : 0<τ) (hraw : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(WeightedGlobalArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).score K|≤lim.word)
    (hnewSpan : A.J*p^(r-1)*p≤I.capacity) :
    LightWeightedGlobalControllerFactory.SpanGuard (config p r I A seed) D lim depth
      (addr I.free I.capacity 8) ν := by sorry
