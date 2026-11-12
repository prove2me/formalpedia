-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stream_rectangle_probability
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.stream_rectangle_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:29:43.566005+00:00
-- url     : https://prove2.me/theorems/ef52c3f1-4fb3-4095-9ce5-19b9c5ad0e72
-- title:
--   BDL26 Countable Embedding Experiment: stream rectangle probability
-- statement:
--   Arbitrary selected finite whole-table rectangles, including the empty set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L86-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L86-L90

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.stream_rectangle_probability {L : ℝ} (p : GeometricParameters L)
    (A : Finset ℕ) (B : (n : ℕ) → Set (StageTables p n))
    (hB : ∀ n ∈ A, MeasurableSet (B n)) :
    streamLaw p (Set.pi (A : Set ℕ) B) = ∏ n ∈ A, physicalTableLaw p n (B n) := by sorry
