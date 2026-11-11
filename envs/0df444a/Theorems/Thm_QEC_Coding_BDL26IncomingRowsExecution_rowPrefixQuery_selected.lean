-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowPrefixQuery_selected
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowPrefixQuery_selected
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:29:13.876904+00:00
-- url     : https://prove2.me/theorems/fe29b1a7-430a-4234-a047-0a9edba400bd
-- title:
--   BDL26 Incoming Rows Execution: row Prefix Query selected
-- statement:
--   Every finite first-bad selection, including the final clean scan, is the original one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1424-L1432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1424-L1432

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowPrefixQuery_selected (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    (rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1
      (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 T s).1).1=
      selected (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T s := by sorry
