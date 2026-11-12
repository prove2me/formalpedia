-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stagePrefix_read
-- name    : QEC.Coding.BDL26PaidRowsComposition.stagePrefix_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:58:33.596439+00:00
-- url     : https://prove2.me/theorems/dc06a36c-75da-4d29-8b4c-1b2cabda2d52
-- title:
--   BDL26 Paid Rows Composition: stage Prefix read
-- statement:
--   Both the cached sample and its exact original fresh-table address are retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L328-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L328-L332

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.stagePrefix_read {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) (v : Vertex (StagePresentation p i.val)) :
    (stateRowQuery v (stagePrefixRows p N i time z)).1 =
      (stageCounters p N i time z v,(tableAt p N i z) (v,stageCounters p N i time z v)) := by sorry
