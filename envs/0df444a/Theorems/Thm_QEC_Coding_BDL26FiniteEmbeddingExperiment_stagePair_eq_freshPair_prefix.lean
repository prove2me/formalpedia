-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_eq_freshPair_prefix
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stagePair_eq_freshPair_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:14:21.450226+00:00
-- url     : https://prove2.me/theorems/7cef1c4a-fc93-47b6-bc99-cfeedd211bee
-- title:
--   BDL26 Finite Embedding Experiment: stage Pair eq fresh Pair prefix
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the stage Pair eq fresh Pair prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L180-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L180-L189

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stagePair_eq_freshPair_prefix {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    stagePair p n i = (freshPair p i.val) ∘ experimentPrefix p (i.val+1) n i.isLt := by sorry
