-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_tableAt_truncate
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.tableAt_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:53:58.779857+00:00
-- url     : https://prove2.me/theorems/70c137df-cd2f-43b5-96f0-b1622efd9fe0
-- title:
--   BDL26 Countable Embedding Experiment: table At truncate
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the table At truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L168-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment/Core.lean#L168-L172

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.tableAt_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (omega : Omega p) : tableAt p n i (truncate p n omega) = omega i.val := by sorry
