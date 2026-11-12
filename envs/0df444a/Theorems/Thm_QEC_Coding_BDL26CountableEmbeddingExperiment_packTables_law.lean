-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_packTables_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.packTables_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:07:23.048306+00:00
-- url     : https://prove2.me/theorems/d85f42d3-51b8-4356-8505-72d25bd7149c
-- title:
--   BDL26 Countable Embedding Experiment: pack Tables law
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the pack Tables law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L42-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L42-L48

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.packTables_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (Measure.pi (fun i : Fin n => physicalTableLaw p i.val)).map (packTables p n) =
      experimentLaw p n := by sorry
