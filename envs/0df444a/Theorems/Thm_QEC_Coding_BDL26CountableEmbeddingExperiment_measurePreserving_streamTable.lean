-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurePreserving_streamTable
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurePreserving_streamTable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:05:58.26873+00:00
-- url     : https://prove2.me/theorems/172364aa-efab-4ff7-9fe4-9baab8681da2
-- title:
--   BDL26 Countable Embedding Experiment: measure Preserving stream Table
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measure Preserving stream Table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L77-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L77-L79

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurePreserving_streamTable {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurePreserving (fun omega : Omega p => omega n) (streamLaw p) (physicalTableLaw p n) := by sorry
