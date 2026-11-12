-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStepQuery_cost_le
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowStepQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:01:19.87842+00:00
-- url     : https://prove2.me/theorems/fedcf3f4-3ddd-4abb-b52e-a6fbc0b5ac93
-- title:
--   BDL26 Incoming Rows Execution: row Step Query cost le
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Step Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L580-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L580-L585

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowStepQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    (rowStepQuery P I r lambda K events T R).2 ≤
      accessMultiplier I*(actualStepQuery P (statePoints I) r lambda K events T R).2 := by sorry
