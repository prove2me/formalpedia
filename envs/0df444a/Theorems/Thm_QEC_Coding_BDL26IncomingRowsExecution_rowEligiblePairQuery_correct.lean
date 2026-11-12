-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowEligiblePairQuery_correct
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowEligiblePairQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:18:24.719753+00:00
-- url     : https://prove2.me/theorems/cc3e08a7-f228-4baf-934d-6b3d57b147a1
-- title:
--   BDL26 Incoming Rows Execution: row Eligible Pair Query correct
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Eligible Pair Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1402-L1407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1402-L1407

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowEligiblePairQuery_correct (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (a b : Triangle P) :
    (rowEligiblePairQuery P I r a b).1=true ↔
      triangleColor P a=triangleColor P b ∧ dist (oldAnchor P (statePoints I) a) (oldAnchor P (statePoints I) b)≤r := by sorry
