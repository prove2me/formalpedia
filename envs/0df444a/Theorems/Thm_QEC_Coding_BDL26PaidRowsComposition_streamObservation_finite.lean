-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamObservation_finite
-- name    : QEC.Coding.BDL26PaidRowsComposition.streamObservation_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:01:11.607357+00:00
-- url     : https://prove2.me/theorems/07029f63-8f81-4712-ad38-dac5e47c5ed3
-- title:
--   BDL26 Paid Rows Composition: stream Observation finite
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stream Observation finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L708-L716
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L708-L716

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

theorem QEC.Coding.BDL26PaidRowsComposition.streamObservation_finite {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamObservation p N omega = finiteObservation p N (BDL26CountableEmbeddingExperiment.truncate p N omega) := by sorry
