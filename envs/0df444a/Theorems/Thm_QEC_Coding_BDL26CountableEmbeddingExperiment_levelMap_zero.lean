-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_zero
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:59:27.843241+00:00
-- url     : https://prove2.me/theorems/151be57c-e08b-4987-b6cb-179c5f8d06af
-- title:
--   BDL26 Countable Embedding Experiment: level Map zero
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the level Map zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L104-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L104-L105

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_zero {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    levelMap p omega 0 = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) := by sorry

attribute [defeq] QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_zero
