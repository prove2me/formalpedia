-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowScanQuery_prefix
-- name    : QEC.Coding.BDL26IncomingRowsExecution.measurable_rowScanQuery_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:48:18.656663+00:00
-- url     : https://prove2.me/theorems/5248a554-9c5a-41f6-9221-51bc254947ae
-- title:
--   BDL26 Incoming Rows Execution: measurable row Scan Query prefix
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the measurable row Scan Query prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1015-L1034
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1015-L1034

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

theorem QEC.Coding.BDL26IncomingRowsExecution.measurable_rowScanQuery_prefix (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let I := incomingRows P w.1
      let R := (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 s).1
      let q := rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R
      (q.1.map (eventToMaster P (statePoints I) r),q.2)) := by sorry
