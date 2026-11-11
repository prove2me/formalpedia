-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_restrictTables
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_restrictTables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:56:30.775322+00:00
-- url     : https://prove2.me/theorems/efd824ae-0459-442d-9e47-611e60fb6e92
-- title:
--   BDL26 Countable Embedding Experiment: measurable restrict Tables
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable restrict Tables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L133-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L133-L135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_restrictTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (restrictTables p n) := by sorry
