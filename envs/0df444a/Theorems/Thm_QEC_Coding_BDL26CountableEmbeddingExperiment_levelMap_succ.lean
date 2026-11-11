-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_succ
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:06:29.555699+00:00
-- url     : https://prove2.me/theorems/280cc814-cb57-4967-a938-16800118fd48
-- title:
--   BDL26 Countable Embedding Experiment: level Map succ
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the level Map succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L107-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L107-L108

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_succ {L : ℝ} (p : GeometricParameters L) (omega : Omega p) (n : ℕ) :
    levelMap p omega (n+1) = physicalSuccessorOutput p n (levelMap p omega n) (omega n) := by sorry
