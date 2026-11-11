-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_finiteSuccess
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurableSet_finiteSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:19:28.270963+00:00
-- url     : https://prove2.me/theorems/6e564d0f-61ed-483c-866c-b1a51062bb59
-- title:
--   BDL26 Finite Embedding Experiment: measurable Set finite Success
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measurable Set finite Success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L56-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L56-L79

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurableSet_finiteSuccess {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet (finiteSuccess p n) := by sorry
