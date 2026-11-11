-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowMasterScan_original
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowMasterScan_original
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:22:56.817669+00:00
-- url     : https://prove2.me/theorems/379ac76d-0a72-4570-ae42-416c07405beb
-- title:
--   BDL26 Incoming Rows Execution: row Master Scan original
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Master Scan original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L961-L969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L961-L969

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowMasterScan_original (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (R : StateRows P) :
    scanQuery (rowMasterStateEventQuery P I lambda K) (rowMasterUniverseQuery P I r).1 R=
      ((rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R).1.map
        (eventToMaster P (statePoints I) r),
       (rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R).2) := by sorry
