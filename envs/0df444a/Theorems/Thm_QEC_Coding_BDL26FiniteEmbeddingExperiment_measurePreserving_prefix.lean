-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_prefix
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurePreserving_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:15:41.056939+00:00
-- url     : https://prove2.me/theorems/aeebf260-218f-4f0a-9ba8-a4e710b7c17e
-- title:
--   BDL26 Finite Embedding Experiment: measure Preserving prefix
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measure Preserving prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L34-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L34-L51

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurePreserving_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    MeasurePreserving (experimentPrefix p m n h) (experimentLaw p n) (experimentLaw p m) := by sorry
