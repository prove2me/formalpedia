-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_reads
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:27.668833+00:00
-- url     : https://prove2.me/theorems/fdfe390d-db5e-46c6-bf31-05243aadfcd3
-- title:
--   Weighted Global Arena Score Scan: reads
-- statement:
--   The Weighted Global Arena Score Scan construction uses the reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L128-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L128-L144

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaScoreScan.reads {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K n U : ℕ} {μ ν : ℕ→ℤ} (h : Invariant I (values D K) μ n ν)
    (hf : ∀i < n, |D.flag i|≤1) (hb : ∀i < n, |D.scoreB i|≤U)
    (hc : ∀i < n, |D.scoreC i|≤U) (hp : ∀i < n, |D.scoreP K i|≤U) :
    (∀i < n, ν ((config p r I A 0).flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
    (∀i < n, ν ((config p r I A 0).scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U) := by sorry
