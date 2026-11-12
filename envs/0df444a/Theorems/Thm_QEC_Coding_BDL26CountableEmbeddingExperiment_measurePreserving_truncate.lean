-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurePreserving_truncate
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurePreserving_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:28:10.101829+00:00
-- url     : https://prove2.me/theorems/68a7b647-3899-43f7-aa6f-baf66c99a159
-- title:
--   BDL26 Countable Embedding Experiment: measure Preserving truncate
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measure Preserving truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L73-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L73-L75

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurePreserving_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurePreserving (truncate p n) (streamLaw p) (experimentLaw p n) := by sorry
