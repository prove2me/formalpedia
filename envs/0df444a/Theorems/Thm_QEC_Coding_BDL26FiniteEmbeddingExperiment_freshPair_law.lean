-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_freshPair_law
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.freshPair_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:14:06.145641+00:00
-- url     : https://prove2.me/theorems/32fb4a90-9658-4d20-be15-8f8002df5955
-- title:
--   BDL26 Finite Embedding Experiment: fresh Pair law
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the fresh Pair law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L164-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L164-L178

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.freshPair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p (n+1)).map (freshPair p n) =
      (outputLaw p n).prod (physicalTableLaw p n) := by sorry
