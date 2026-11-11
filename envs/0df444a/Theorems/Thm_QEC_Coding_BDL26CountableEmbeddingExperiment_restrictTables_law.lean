-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_restrictTables_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.restrictTables_law
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:05:44.606827+00:00
-- url     : https://prove2.me/theorems/c6a92b81-14d6-40aa-8049-0f5ce9be3eed
-- title:
--   BDL26 Countable Embedding Experiment: restrict Tables law
-- statement:
--   Injective restriction of the genuine infinite product, not a supplied marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L51-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L51-L62

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.restrictTables_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (restrictTables p n) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val) := by sorry
