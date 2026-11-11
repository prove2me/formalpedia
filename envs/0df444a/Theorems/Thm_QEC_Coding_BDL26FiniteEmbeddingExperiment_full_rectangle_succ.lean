-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_full_rectangle_succ
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.full_rectangle_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:19:00.348049+00:00
-- url     : https://prove2.me/theorems/163941e4-d017-48cc-a1bd-0c77b6c00e89
-- title:
--   BDL26 Finite Embedding Experiment: full rectangle succ
-- statement:
--   The full dependent rectangle splits into the preceding rectangle and final table set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L68-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L68-L81

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.full_rectangle_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin (n+1)) → Set (StageTables p i.val)) :
    {z : Experiment p (n+1) | ∀ i, tableAt p (n+1) i z ∈ B i} =
      {z : Experiment p n | ∀ i : Fin n, tableAt p n i z ∈ B i.castSucc} ×ˢ
        B (Fin.last n) := by sorry
