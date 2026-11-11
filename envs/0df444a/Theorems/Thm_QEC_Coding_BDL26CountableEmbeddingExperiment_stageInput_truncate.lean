-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stageInput_truncate
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.stageInput_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:58:53.550572+00:00
-- url     : https://prove2.me/theorems/7707c9cd-03c1-4d32-9f7f-931c1570b0c7
-- title:
--   BDL26 Countable Embedding Experiment: stage Input truncate
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stage Input truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L126-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L126-L131

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.stageInput_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin n) :
    stageInput p n i (truncate p n omega) = levelMap p omega i.val := by sorry
