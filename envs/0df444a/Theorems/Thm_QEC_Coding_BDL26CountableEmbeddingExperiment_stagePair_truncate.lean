-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stagePair_truncate
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.stagePair_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:08:24.894919+00:00
-- url     : https://prove2.me/theorems/49e7bb17-7ab1-48a2-b20f-ed368ccdfa7b
-- title:
--   BDL26 Countable Embedding Experiment: stage Pair truncate
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stage Pair truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L133-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L133-L138

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.stagePair_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin n) :
    stagePair p n i (truncate p n omega) = (levelMap p omega i.val, omega i.val) := by sorry
