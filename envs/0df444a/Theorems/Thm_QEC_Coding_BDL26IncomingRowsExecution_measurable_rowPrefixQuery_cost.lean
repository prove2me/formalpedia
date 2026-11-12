-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowPrefixQuery_cost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.measurable_rowPrefixQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:26:35.491387+00:00
-- url     : https://prove2.me/theorems/fbaa6a71-3535-450f-99ce-2a5824f23aff
-- title:
--   BDL26 Incoming Rows Execution: measurable row Prefix Query cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the measurable row Prefix Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1065-L1078
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1065-L1078

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

theorem QEC.Coding.BDL26IncomingRowsExecution.measurable_rowPrefixQuery_cost (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let I := incomingRows P w.1
      (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 s).2) := by sorry
