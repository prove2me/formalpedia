-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowExecutionCost_finite_of_halts
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowExecutionCost_finite_of_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:22:06.174962+00:00
-- url     : https://prove2.me/theorems/de4edfc6-59ca-4607-965c-e2763dfb9666
-- title:
--   BDL26 Incoming Rows Execution: row Execution Cost finite of halts
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Execution Cost finite of halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L701-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L701-L707

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowExecutionCost_finite_of_halts (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space))
    (h : Halts (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T) :
    rowExecutionCost P I hr lambda K T<∞ := by sorry
