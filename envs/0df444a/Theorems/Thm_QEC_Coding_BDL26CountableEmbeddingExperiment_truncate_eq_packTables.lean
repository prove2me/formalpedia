-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_eq_packTables
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_eq_packTables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:55:47.690801+00:00
-- url     : https://prove2.me/theorems/7152a8e2-e0fa-4c4b-9836-196c98cafc35
-- title:
--   BDL26 Countable Embedding Experiment: truncate eq pack Tables
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the truncate eq pack Tables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L124-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L124-L131

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_eq_packTables {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) : truncate p n omega = packTables p n (restrictTables p n omega) := by sorry
