-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamHaltTime
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamHaltTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:12:54.120225+00:00
-- url     : https://prove2.me/theorems/5521fcc9-407a-4c48-aa75-f71018a574ef
-- title:
--   BDL26 Countable Embedding Experiment: measurable stream Halt Time
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable stream Halt Time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L273-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L273-L275

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamHaltTime p n) := by sorry
