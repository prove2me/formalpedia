-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_tableAt
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurePreserving_tableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:14:09.329902+00:00
-- url     : https://prove2.me/theorems/dceaf15e-499d-45ce-b7b4-c38df64ac0fe
-- title:
--   BDL26 Finite Embedding Experiment: measure Preserving table At
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measure Preserving table At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L53-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L53-L56

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurePreserving_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    MeasurePreserving (tableAt p n i) (experimentLaw p n) (physicalTableLaw p i.val) := by sorry
