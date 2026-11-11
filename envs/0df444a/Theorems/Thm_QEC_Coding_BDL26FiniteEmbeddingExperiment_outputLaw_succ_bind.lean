-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_succ_bind
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_succ_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:27:44.38701+00:00
-- url     : https://prove2.me/theorems/7858ccdf-6963-40db-85a3-16cea30d998d
-- title:
--   BDL26 Finite Embedding Experiment: output Law succ bind
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the output Law succ bind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L212-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L212-L214

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_succ_bind {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    outputLaw p (n+1) = (outputLaw p n).bind (successorKernel p n) := by sorry
