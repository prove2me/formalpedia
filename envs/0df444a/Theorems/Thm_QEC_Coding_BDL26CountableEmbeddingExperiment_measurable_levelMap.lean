-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_levelMap
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_levelMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:01:37.494194+00:00
-- url     : https://prove2.me/theorems/c604312b-8d8b-4888-8860-c0eb3f9ea0ea
-- title:
--   BDL26 Countable Embedding Experiment: measurable level Map
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable level Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L110-L114

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_levelMap {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun omega => levelMap p omega n) := by sorry
