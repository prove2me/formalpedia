-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stream_successor_kernel
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.stream_successor_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:34:22.417385+00:00
-- url     : https://prove2.me/theorems/d08f7c10-71dc-4006-89d2-ff372bc8e896
-- title:
--   BDL26 Countable Embedding Experiment: stream successor kernel
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream successor kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L162-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L162-L166

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.stream_successor_kernel {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => levelMap p omega (n+1)) =
      successorKernel p n ∘ₘ ((streamLaw p).map (fun omega => levelMap p omega n)) := by sorry
