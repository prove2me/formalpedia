-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowEligiblePairQuery_cost_le
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowEligiblePairQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:56:03.590555+00:00
-- url     : https://prove2.me/theorems/7e9d0b91-e4fb-485a-9947-65cb879ed816
-- title:
--   BDL26 Incoming Rows Execution: row Eligible Pair Query cost le
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Eligible Pair Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L248-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L248-L250

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowEligiblePairQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : (rowEligiblePairQuery P I r a b).2 ≤
      accessMultiplier I*(eligiblePairQuery P (statePoints I) r a b).2 := by sorry
