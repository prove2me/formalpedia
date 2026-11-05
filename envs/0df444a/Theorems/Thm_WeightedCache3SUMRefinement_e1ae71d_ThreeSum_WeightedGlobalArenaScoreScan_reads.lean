-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_reads
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:19:44.405121+00:00
-- url     : https://prove2.me/theorems/e15b280a-65c4-4f27-997b-4d2905b20c56
-- title:
--   reads
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L128-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L128-L144

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.reads {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K n U : ℕ} {μ ν : ℕ→ℤ} (h : Invariant I (values D K) μ n ν)
    (hf : ∀i < n, |D.flag i|≤1) (hb : ∀i < n, |D.scoreB i|≤U)
    (hc : ∀i < n, |D.scoreC i|≤U) (hp : ∀i < n, |D.scoreP K i|≤U) :
    (∀i < n, ν ((config p r I A 0).flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
    (∀i < n, ν ((config p r I A 0).scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U) := by sorry
