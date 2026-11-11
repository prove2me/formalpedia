-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_history_truncate
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.history_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:32:27.746178+00:00
-- url     : https://prove2.me/theorems/c7193db7-e2bc-4516-8f53-3354f305adf0
-- title:
--   BDL26 Countable Embedding Experiment: history truncate
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the history truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L119-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L119-L124

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.history_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin (n+1)) :
    history p n (truncate p n omega) i = levelMap p omega i.val := by sorry
