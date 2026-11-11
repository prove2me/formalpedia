-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageSelected_none_iff
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageSelected_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:28:15.791935+00:00
-- url     : https://prove2.me/theorems/35446d45-1cc5-426d-9e7b-643f39ef6fc3
-- title:
--   BDL26 Finite Embedding Experiment: stage Selected none iff
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the stage Selected none iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L81-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L81-L87

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageSelected_none_iff {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) (z : Experiment p n) :
    stageSelected p n i time z = none ↔
      selected (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
        (eventBad (StagePresentation p i.val) (stageInput p n i z)
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time = none := by sorry
