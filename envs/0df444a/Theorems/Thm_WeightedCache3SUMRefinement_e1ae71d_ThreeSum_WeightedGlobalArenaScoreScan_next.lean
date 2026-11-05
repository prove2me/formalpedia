-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_next
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:32.089021+00:00
-- url     : https://prove2.me/theorems/2df4d82e-3e37-4f95-9219-faf4d52c0952
-- title:
--   next
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L148-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L148-L175

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.next {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K i : ℕ} {μ ν ξ : ℕ→ℤ} (hcapacity : 106 ≤ I.capacity) (hi : i < I.capacity)
    (h : Invariant I (values D K) μ i ν) (done : (D.candidate i).Done K ν ξ) :
    Invariant I (values D K) μ (i+1) ξ := by sorry
