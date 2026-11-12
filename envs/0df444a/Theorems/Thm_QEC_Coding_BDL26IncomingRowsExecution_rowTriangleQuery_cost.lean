-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTriangleQuery_cost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowTriangleQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:15:51.212356+00:00
-- url     : https://prove2.me/theorems/40e7fcb8-fe27-4c04-b5b7-ec8d9fdb3fcd
-- title:
--   BDL26 Incoming Rows Execution: row Triangle Query cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Triangle Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L448-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L448-L453

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowTriangleQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (rowTriangleQuery P I lambda t R z).2=(stateTriangleQuery P (statePoints I) lambda t R z).2+
      triangleExtra P I t := by sorry
