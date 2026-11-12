-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamPhysicalProcess
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamPhysicalProcess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:40:12.439553+00:00
-- url     : https://prove2.me/theorems/e731e8ab-ccdf-4645-b471-d048c2d9892b
-- title:
--   BDL26 Countable Embedding Experiment: measurable stream Physical Process
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable stream Physical Process property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L304-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L304-L306

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamPhysicalProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n => streamPhysicalOutput p n omega) := by sorry
