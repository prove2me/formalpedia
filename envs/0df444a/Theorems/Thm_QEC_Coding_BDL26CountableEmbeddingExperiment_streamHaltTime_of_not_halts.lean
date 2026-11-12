-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamHaltTime_of_not_halts
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamHaltTime_of_not_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:10:30.213601+00:00
-- url     : https://prove2.me/theorems/027b86a4-d212-4d21-9133-e0dce345b0db
-- title:
--   BDL26 Countable Embedding Experiment: stream Halt Time of not halts
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Halt Time of not halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L308-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L308-L310

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamHaltTime_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (hh : ¬ streamHalts p n omega) : streamHaltTime p n omega = 0 := by sorry
