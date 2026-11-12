-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurableSet_streamHalts
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurableSet_streamHalts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:33:51.374886+00:00
-- url     : https://prove2.me/theorems/4bced70b-ead6-46a1-a5d6-661088a0404c
-- title:
--   BDL26 Countable Embedding Experiment: measurable Set stream Halts
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable Set stream Halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L269-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L269-L271

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurableSet_streamHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet {omega | streamHalts p n omega} := by sorry
