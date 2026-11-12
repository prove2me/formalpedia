-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurableSet_allFiniteSuccess
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurableSet_allFiniteSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:01:12.987282+00:00
-- url     : https://prove2.me/theorems/e4d94183-ef66-452b-9238-331805640658
-- title:
--   BDL26 Countable Embedding Experiment: measurable Set all Finite Success
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable Set all Finite Success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L30-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L30-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurableSet_allFiniteSuccess {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet (allFiniteSuccess p) := by sorry
