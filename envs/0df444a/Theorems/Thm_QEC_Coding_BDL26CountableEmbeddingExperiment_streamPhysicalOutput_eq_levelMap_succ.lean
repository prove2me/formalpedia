-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamPhysicalOutput_eq_levelMap_succ
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamPhysicalOutput_eq_levelMap_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:31:58.292353+00:00
-- url     : https://prove2.me/theorems/8952163e-b505-4e56-aa9e-cc44c65583bf
-- title:
--   BDL26 Countable Embedding Experiment: stream Physical Output eq level Map succ
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Physical Output eq level Map succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L195-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L195-L200

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamPhysicalOutput_eq_levelMap_succ {L : ℝ} (p : GeometricParameters L)
    (n : ℕ) (omega : Omega p) :
    streamPhysicalOutput p n omega = levelMap p omega (n+1) := by sorry
