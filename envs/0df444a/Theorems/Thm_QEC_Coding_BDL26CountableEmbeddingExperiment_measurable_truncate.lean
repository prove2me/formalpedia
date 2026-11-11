-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:53:29.403149+00:00
-- url     : https://prove2.me/theorems/b0de375d-0fc1-42a1-8059-94c1ecc88936
-- title:
--   BDL26 Countable Embedding Experiment: measurable truncate
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L137-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L137-L144

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (truncate p n) := by sorry
