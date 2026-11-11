-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowEligibleListQuery_cost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowEligibleListQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:26:26.470259+00:00
-- url     : https://prove2.me/theorems/7342e33f-dd42-4d43-a59c-862c829c8e0f
-- title:
--   BDL26 Incoming Rows Execution: row Eligible List Query cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Eligible List Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L748-L759
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L748-L759

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowEligibleListQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowEligibleListQuery P I r L).2=
      (eligibleListQuery P (statePoints I) r L).2+eligibilityExtra P I L := by sorry
