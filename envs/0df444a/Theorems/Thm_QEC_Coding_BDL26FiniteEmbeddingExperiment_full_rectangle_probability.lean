-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_full_rectangle_probability
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.full_rectangle_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:14:26.745171+00:00
-- url     : https://prove2.me/theorems/0f18dc44-fbe1-49c4-b8ad-42c54c432f50
-- title:
--   BDL26 Finite Embedding Experiment: full rectangle probability
-- statement:
--   Arbitrary table rectangles have the actual product probability, including zero stages.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L84-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L84-L102

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.full_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n {z | ∀ i, tableAt p n i z ∈ B i} =
      ∏ i : Fin n, physicalTableLaw p i.val (B i) := by sorry
