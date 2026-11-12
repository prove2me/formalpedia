-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stream_successor_bind
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.stream_successor_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:31:53.369746+00:00
-- url     : https://prove2.me/theorems/54c263d1-59d8-4ccd-b955-0c2ce75e901d
-- title:
--   BDL26 Countable Embedding Experiment: stream successor bind
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream successor bind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L168-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L168-L172

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.stream_successor_bind {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => levelMap p omega (n+1)) =
      ((streamLaw p).map (fun omega => levelMap p omega n)).bind (successorKernel p n) := by sorry
