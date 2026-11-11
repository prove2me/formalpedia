-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_law
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:56:49.199563+00:00
-- url     : https://prove2.me/theorems/f6e4bbe9-2337-4528-ae9a-b6ecaaa12c20
-- title:
--   BDL26 Countable Embedding Experiment: truncate law
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the truncate law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L64-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L64-L71

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (truncate p n) = experimentLaw p n := by sorry
