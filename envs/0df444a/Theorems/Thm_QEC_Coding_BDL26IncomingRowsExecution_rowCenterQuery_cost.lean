-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowCenterQuery_cost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowCenterQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:47:45.588749+00:00
-- url     : https://prove2.me/theorems/cd004276-d8d0-4087-8fc0-2fa834b46b37
-- title:
--   BDL26 Incoming Rows Execution: row Center Query cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Center Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L378-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L378-L381

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowCenterQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) :
    (rowCenterQuery P I lambda K a g).2=(fullCenterQuery P (statePoints I) lambda K a g).2+
      centerExtra P I a := by sorry
