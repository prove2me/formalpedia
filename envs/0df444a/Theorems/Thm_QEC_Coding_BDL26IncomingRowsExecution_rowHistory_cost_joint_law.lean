-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowHistory_cost_joint_law
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowHistory_cost_joint_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:15:50.176234+00:00
-- url     : https://prove2.me/theorems/0bb64c87-977d-4b8a-81a4-699c92031963
-- title:
--   BDL26 Incoming Rows Execution: row History cost joint law
-- statement:
--   Complete original history jointly with the new actual cost vector and total.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1321-L1326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1321-L1326

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowHistory_cost_joint_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (fun z => (rowHistory p N z,(fun i => rowStageCost p N i z),rowTotalCost p N z))=
      (experimentLaw p N).map (fun z => (history p N z,(fun i => rowStageCost p N i z),rowTotalCost p N z)) := by sorry
