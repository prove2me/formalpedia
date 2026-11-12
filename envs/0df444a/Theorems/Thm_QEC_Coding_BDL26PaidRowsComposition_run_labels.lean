-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_run_labels
-- name    : QEC.Coding.BDL26PaidRowsComposition.run_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:32:15.206594+00:00
-- url     : https://prove2.me/theorems/0d2b77de-5941-4efa-bf29-10b7008b287e
-- title:
--   BDL26 Paid Rows Composition: run labels
-- statement:
--   The BDL26 Paid Rows Composition construction uses the run labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L118-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L118-L120

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

theorem QEC.Coding.BDL26PaidRowsComposition.run_labels {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    ((run p N z).1).map Prod.fst = vertexInputList (StagePresentation p N) := by sorry
