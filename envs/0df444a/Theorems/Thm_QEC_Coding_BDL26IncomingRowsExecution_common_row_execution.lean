-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_common_row_execution
-- name    : QEC.Coding.BDL26IncomingRowsExecution.common_row_execution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:18:11.985104+00:00
-- url     : https://prove2.me/theorems/20517be1-7882-449e-b732-96123e33a709
-- title:
--   BDL26 Incoming Rows Execution: common row execution
-- statement:
--   Every prefix reads the literal truncation of the same original countable stream.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1392-L1399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1392-L1399

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

theorem QEC.Coding.BDL26IncomingRowsExecution.common_row_execution {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, rowTotalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega)<∞) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by sorry
