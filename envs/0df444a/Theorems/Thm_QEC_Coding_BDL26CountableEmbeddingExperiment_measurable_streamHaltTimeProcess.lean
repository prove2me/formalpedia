-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamHaltTimeProcess
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamHaltTimeProcess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:39:03.43226+00:00
-- url     : https://prove2.me/theorems/112b2dbd-4981-4c6d-b4ca-c559fbf26c06
-- title:
--   BDL26 Countable Embedding Experiment: measurable stream Halt Time Process
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable stream Halt Time Process property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L300-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L300-L302

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamHaltTimeProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n => streamHaltTime p n omega) := by sorry
