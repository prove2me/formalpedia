-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageGeometricOutput_of_not_halts
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageGeometricOutput_of_not_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:17:37.526887+00:00
-- url     : https://prove2.me/theorems/3b68856a-c2ba-4e32-ab69-1236a29137a4
-- title:
--   BDL26 Finite Embedding Experiment: stage Geometric Output of not halts
-- statement:
--   Nonhalting tables return the original assignment at the zero counters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L75-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L75-L79

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageGeometricOutput_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p n) (hh : ¬ stageHalts p n i z) :
    stageGeometricOutput p n i z = assignment (tableAt p n i z) (fun _ => 0) := by sorry
