-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePhysicalOutput_rx
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stagePhysicalOutput_rx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:45:02.932359+00:00
-- url     : https://prove2.me/theorems/d9d03abb-0809-45a1-a208-5c8768cbdd22
-- title:
--   BDL26 Finite Embedding Experiment: stage Physical Output rx
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the stage Physical Output rx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L218-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L218-L223

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stagePhysicalOutput_rx {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (h : i.val % 2 = 0) (z : Experiment p n) :
    stagePhysicalOutput p n i z = fun v =>
      rxVertexPoint _ (perturbationOddScale p) (stagePerturbedOutput p n i z)
        (nextRXVertex _ i.val (state (perturbationOddScale p) i.val) h v) := by sorry
