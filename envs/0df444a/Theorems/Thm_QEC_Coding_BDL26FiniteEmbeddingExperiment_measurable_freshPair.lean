-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_freshPair
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_freshPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:15:32.96677+00:00
-- url     : https://prove2.me/theorems/a4089d7b-31a0-4951-bbae-9856afe173e0
-- title:
--   BDL26 Finite Embedding Experiment: measurable fresh Pair
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measurable fresh Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L160-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L160-L162

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (freshPair p n) := by sorry
