-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageHaltTime_of_not_halts
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageHaltTime_of_not_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:16:38.065604+00:00
-- url     : https://prove2.me/theorems/8ad259ab-c9da-4aca-b7ae-3c24c37d78ad
-- title:
--   BDL26 Finite Embedding Experiment: stage Halt Time of not halts
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the stage Halt Time of not halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L68-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L68-L72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageHaltTime_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p n) (hh : ¬ stageHalts p n i z) :
    stageHaltTime p n i z = 0 := by sorry
