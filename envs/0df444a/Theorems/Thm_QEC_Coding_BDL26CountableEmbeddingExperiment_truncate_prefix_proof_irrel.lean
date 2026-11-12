-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_prefix_proof_irrel
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_prefix_proof_irrel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:26:13.505591+00:00
-- url     : https://prove2.me/theorems/1688eab7-2d5a-44f3-8e28-3ec4b3b1e30a
-- title:
--   BDL26 Countable Embedding Experiment: truncate prefix proof irrel
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the truncate prefix proof irrel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L163-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L163-L166

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_prefix_proof_irrel {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h h' : m ≤ n) (omega : Omega p) :
    experimentPrefix p m n h (truncate p n omega) =
      experimentPrefix p m n h' (truncate p n omega) := by sorry
