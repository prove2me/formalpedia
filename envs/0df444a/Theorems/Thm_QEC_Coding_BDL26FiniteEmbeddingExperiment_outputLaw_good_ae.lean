-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_good_ae
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_good_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:20:17.687247+00:00
-- url     : https://prove2.me/theorems/e0b180bf-021f-4d07-bb75-0da26fb0fa05
-- title:
--   BDL26 Finite Embedding Experiment: output Law good ae
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the output Law good ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L21-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L21-L30

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ J ∂outputLaw p n, IsBoundedDensityLocalMap (StagePresentation p n) J p.t := by sorry
