-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_seed_sharp
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.seed_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:45:09.468536+00:00
-- url     : https://prove2.me/theorems/27ff52cd-2191-4f88-8552-da94619a4454
-- title:
--   BDL26 Countable Embedding Experiment: seed sharp
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the seed sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L141-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L141-L150

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.seed_sharp {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    Fintype.card (Physical (perturbationOddScale p) 0) = 5 ∧
    (∀ q : Physical (perturbationOddScale p) 0, levelMap p omega 0 (.q q) = 0) ∧
    (∀ r s : Physical (perturbationOddScale p) 0,
      dist (levelMap p omega 0 (.q r)) (levelMap p omega 0 (.q s)) = 0) ∧
    ∀ c, ((qubitHits (StagePresentation p 0) (levelMap p omega 0)
      (Metric.closedBall c 1)).card : ℝ) ≤ 5 := by sorry
