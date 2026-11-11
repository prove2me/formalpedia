-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageSelected_original
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageSelected_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:28:03.357324+00:00
-- url     : https://prove2.me/theorems/e9e82487-9fb9-4cda-8a43-bfe74b6c351f
-- title:
--   BDL26 Finite Embedding Experiment: stage Selected original
-- statement:
--   Pointwise original-label conjugacy, including `none`, `some` and nonhalting inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L60-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L60-L66

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageSelected_original {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) (z : Experiment p n) :
    stageSelected p n i time z =
      selected (masterSupport (StagePresentation p i.val))
        (masterBad (StagePresentation p i.val) (anchorRadius p.m) p.lambda
          ((6*p.m+2)*p.lambda) (stageInput p n i z)) (tableAt p n i z) time := by sorry
