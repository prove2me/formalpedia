-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamSelected_original
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamSelected_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:32:24.286391+00:00
-- url     : https://prove2.me/theorems/1f0ea5d5-e83f-40b5-97f4-4bbf3a52c0b2
-- title:
--   BDL26 Countable Embedding Experiment: stream Selected original
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Selected original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L202-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L202-L209

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamSelected_original {L : ℝ} (p : GeometricParameters L)
    (n time : ℕ) (omega : Omega p) :
    streamSelected p n time omega =
      selected (masterSupport (StagePresentation p n))
        (masterBad (StagePresentation p n) (anchorRadius p.m) p.lambda
          ((6*p.m+2)*p.lambda) (levelMap p omega n)) (omega n) time := by sorry
