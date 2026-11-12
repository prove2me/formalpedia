-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_original_stream_prefix
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.original_stream_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:13:01.237805+00:00
-- url     : https://prove2.me/theorems/c7b153fc-aba8-4b15-913d-4f7788112987
-- title:
--   BDL26 Countable Embedding Experiment: original stream prefix
-- statement:
--   The finite original execution is the same stream execution on every prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L212-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L212-L253

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.original_stream_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (time : ℕ) (omega : Omega p) :
    streamCounters p i.val time omega = stageCounters p N i time (truncate p N omega) ∧
    streamSelected p i.val time omega = stageSelected p N i time (truncate p N omega) ∧
    (streamHalts p i.val omega ↔ stageHalts p N i (truncate p N omega)) ∧
    streamHaltTime p i.val omega = stageHaltTime p N i (truncate p N omega) ∧
    streamGeometricOutput p i.val omega = stageGeometricOutput p N i (truncate p N omega) ∧
    streamPerturbedOutput p i.val omega = stagePerturbedOutput p N i (truncate p N omega) ∧
    streamPhysicalOutput p i.val omega = stagePhysicalOutput p N i (truncate p N omega) := by sorry
