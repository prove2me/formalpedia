-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_zero
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:11:49.777076+00:00
-- url     : https://prove2.me/theorems/979ce0f5-4e9b-479a-a788-bd35e90b81e3
-- title:
--   BDL26 Finite Embedding Experiment: output Law zero
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the output Law zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L151-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L151-L154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_zero {L : ℝ} (p : GeometricParameters L) :
    outputLaw p 0 = Measure.dirac (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) := by sorry
