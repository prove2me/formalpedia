-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_incomingRead_cost_map
-- name    : QEC.Coding.BDL26IncomingRowsExecution.incomingRead_cost_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:22:45.064881+00:00
-- url     : https://prove2.me/theorems/1fef4907-7354-47fb-bd07-b6dc4c3b4363
-- title:
--   BDL26 Incoming Rows Execution: incoming Read cost map
-- statement:
--   Lookup cost depends only on labels, independently of stored points and counters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L904-L915
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L904-L915

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

theorem QEC.Coding.BDL26IncomingRowsExecution.incomingRead_cost_map (P : TannerSquarePresentation) (v : Vertex P)
    (L : List (Vertex P)) (f g : Vertex P → ℕ × Space) :
    (incomingRead P (L.map (fun u => (u,f u))) v).2=
      (incomingRead P (L.map (fun u => (u,g u))) v).2 := by sorry
