-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaControllerCore_scan_guard
-- name    : ThreeSum.WeightedGlobalArenaControllerCore.scan_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:49:20.465741+00:00
-- url     : https://prove2.me/theorems/9aa41cb4-e2ad-4d4d-b27e-dc27fd35f7d9
-- title:
--   Weighted Global Arena Controller Core: scan guard
-- statement:
--   The Weighted Global Arena Controller Core construction uses the scan guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L72-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L72-L83

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaControllerCore.scan_guard {lim : Limits} {depth K U n positionCap i : ℕ}
    {maps : Fin F→Weight m p} {τ cap : ℕ} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {I : Input} {A : Inputs} {D : (seed : ℕ)→Data (config p r I A seed)}
    {μ ν : ℕ→ℤ} {L R : ℕ→ℕ→ℤ}
    (H : InputsReady (lim := lim) (depth := depth) (K := K) (U := U) (n := n) (positionCap := positionCap)
      maps τ cap Q I A D μ L R)
    (hi : i < n)
    (h : Invariant I (values (family maps τ cap U Q I A D L R) K) μ i ν) :
    ((family maps τ cap U Q I A D L R).candidate i).Guard lim (depth+1) K
      (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
      (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) ν := by sorry
