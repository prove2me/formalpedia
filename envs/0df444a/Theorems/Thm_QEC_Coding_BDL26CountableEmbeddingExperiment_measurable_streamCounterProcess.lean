-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamCounterProcess
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamCounterProcess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:37:18.856784+00:00
-- url     : https://prove2.me/theorems/80ca3c1e-ee01-4bfc-8755-e3092d995c7a
-- title:
--   BDL26 Countable Embedding Experiment: measurable stream Counter Process
-- statement:
--   All stages and all execution times form one jointly measurable observation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L290-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L290-L293

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamCounterProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n time => streamCounters p n time omega) := by sorry
