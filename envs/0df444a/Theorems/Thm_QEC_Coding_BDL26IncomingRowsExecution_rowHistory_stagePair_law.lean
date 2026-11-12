-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowHistory_stagePair_law
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowHistory_stagePair_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:12:35.175588+00:00
-- url     : https://prove2.me/theorems/f239174c-aeaa-4198-9b5e-974985ac0a09
-- title:
--   BDL26 Incoming Rows Execution: row History stage Pair law
-- statement:
--   The row-driven history uses the original independent whole-table factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1309-L1318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1309-L1318

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowHistory_stagePair_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    (experimentLaw p N).map (fun z =>
      (rowEvaluate p i.val (experimentPrefix p i.val N (by omega) z),tableAt p N i z))=
      (outputLaw p i.val).prod (physicalTableLaw p i.val) := by sorry
