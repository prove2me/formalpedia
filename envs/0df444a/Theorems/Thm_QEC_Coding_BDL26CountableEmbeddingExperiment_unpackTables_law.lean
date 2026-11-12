-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_unpackTables_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.unpackTables_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:06:05.735425+00:00
-- url     : https://prove2.me/theorems/9b1e2769-3f1c-425f-baf8-7d835bfb4af2
-- title:
--   BDL26 Countable Embedding Experiment: unpack Tables law
-- statement:
--   The original nested law, read as its full dependent vector, is the product law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L29-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L29-L40

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.unpackTables_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p n).map (unpackTables p n) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val) := by sorry
