-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_iIndepFun
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:17:43.740413+00:00
-- url     : https://prove2.me/theorems/27bda5f2-b02f-4420-9c31-107261eb7f2c
-- title:
--   BDL26 Finite Embedding Experiment: table At i Indep Fun
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the table At i Indep Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L135-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L135-L142

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_iIndepFun {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    iIndepFun (tableAt p n) (experimentLaw p n) := by sorry
