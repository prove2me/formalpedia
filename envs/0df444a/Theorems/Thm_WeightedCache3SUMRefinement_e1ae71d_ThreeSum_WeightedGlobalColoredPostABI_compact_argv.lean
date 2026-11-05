-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPostABI_compact_argv
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.compact_argv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:01.816047+00:00
-- url     : https://prove2.me/theorems/b3a32cbe-a747-4d7c-9bf9-7346c91546bd
-- title:
--   compact_argv
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPostABI.lean#L97-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPostABI.lean#L97-L103

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.compact_argv {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input) (nB nC : ℕ) :
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q {I with nB:=nB,nC:=nC})).argv=
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q I)).argv := by sorry
