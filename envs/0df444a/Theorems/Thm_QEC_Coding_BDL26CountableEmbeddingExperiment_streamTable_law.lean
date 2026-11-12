-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamTable_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamTable_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:29:33.512235+00:00
-- url     : https://prove2.me/theorems/9a0ac04b-993e-4382-956e-ace2c6a23622
-- title:
--   BDL26 Countable Embedding Experiment: stream Table law
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Table law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L81-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L81-L83

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamTable_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => omega n) = physicalTableLaw p n := by sorry
