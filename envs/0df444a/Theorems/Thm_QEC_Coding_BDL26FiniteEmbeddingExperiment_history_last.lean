-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_last
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.history_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:19:25.654286+00:00
-- url     : https://prove2.me/theorems/ef43ee4b-7fbf-4f64-950c-6b4cb18af125
-- title:
--   BDL26 Finite Embedding Experiment: history last
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the history last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L153-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L153-L155

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.history_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) : history p n z (Fin.last n) = evaluate p n z := by sorry
