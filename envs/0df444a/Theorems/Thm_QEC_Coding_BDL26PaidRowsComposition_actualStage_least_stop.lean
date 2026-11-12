-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStage_least_stop
-- name    : QEC.Coding.BDL26PaidRowsComposition.actualStage_least_stop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:35:51.054921+00:00
-- url     : https://prove2.me/theorems/70525613-cad1-4f89-9b4f-39988ae790be
-- title:
--   BDL26 Paid Rows Composition: actual Stage least stop
-- statement:
--   Least stopping time includes the final clean scan and all preceding first-bad scans.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L429-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L429-L444

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.actualStage_least_stop {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : actualStageHalts p N i z) :
    actualStageSelected p N i (actualStageHaltTime p N i z) z = none ∧
      ∀ time < actualStageHaltTime p N i z, actualStageSelected p N i time z ≠ none := by sorry
