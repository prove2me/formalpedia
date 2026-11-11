-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_prefix
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:01:28.738978+00:00
-- url     : https://prove2.me/theorems/9d0ac472-305d-492f-b631-48d26576c372
-- title:
--   BDL26 Countable Embedding Experiment: truncate prefix
-- statement:
--   All finite prefix equations hold at every stream, even on exceptional tables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L147-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L147-L161

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (omega : Omega p) :
    experimentPrefix p m n h (truncate p n omega) = truncate p m omega := by sorry
