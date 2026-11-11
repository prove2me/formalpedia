-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_output_law
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_output_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:17:20.674519+00:00
-- url     : https://prove2.me/theorems/3e53d2f0-87e7-42e7-bf83-95b6b4fa8b00
-- title:
--   BDL26 Finite Embedding Experiment: prefix output law
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the prefix output law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L198-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L198-L203

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_output_law {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    (experimentLaw p n).map ((evaluate p m) ∘ experimentPrefix p m n h) = outputLaw p m := by sorry
