-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowMasterUniverseQuery_original
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowMasterUniverseQuery_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:48:58.021918+00:00
-- url     : https://prove2.me/theorems/6947854d-a058-4077-9d15-77c601511274
-- title:
--   BDL26 Incoming Rows Execution: row Master Universe Query original
-- statement:
--   Conjugacy includes both original priority and every new numeric lookup cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L832-L839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L832-L839

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26IncomingRowsExecution.rowMasterUniverseQuery_original (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : rowMasterUniverseQuery P I r=
      ((rowUniverseQuery P I hr).1.map (eventToMaster P (statePoints I) r),
       (rowUniverseQuery P I hr).2) := by sorry
