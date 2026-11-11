-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finite_rectangle_probability
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.finite_rectangle_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:15:25.993892+00:00
-- url     : https://prove2.me/theorems/ad971a09-f42c-4953-8193-b4333aa4ae9d
-- title:
--   BDL26 Finite Embedding Experiment: finite rectangle probability
-- statement:
--   Every selected finite rectangle factors; unused factors remain the original whole laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L105-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L105-L133

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.finite_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (A : Finset (Fin n)) (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n (⋂ i ∈ A, tableAt p n i ⁻¹' B i) =
      ∏ i ∈ A, physicalTableLaw p i.val (B i) := by sorry
