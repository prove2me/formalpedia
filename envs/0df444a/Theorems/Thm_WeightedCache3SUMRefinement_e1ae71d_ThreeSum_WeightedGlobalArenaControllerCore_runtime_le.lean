-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaControllerCore_runtime_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore.runtime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:04.416775+00:00
-- url     : https://prove2.me/theorems/ef549f59-8ec1-4435-b602-ee91fec8f21a
-- title:
--   runtime_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L32-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L32-L36

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore.runtime_le {C : Config} [Fact C.p.Prime] (D : Family C)
    (K R S n : ℕ) (raws : List ℤ) (words maps : List ℕ) (i : ℕ) (hi : i < n) :
    (D.candidate i).runtime K R S raws words maps ≤ seedTime D K R S n raws words maps := by sorry
