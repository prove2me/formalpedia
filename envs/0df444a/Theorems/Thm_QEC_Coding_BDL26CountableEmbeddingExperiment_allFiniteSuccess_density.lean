-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_density
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:43:42.161468+00:00
-- url     : https://prove2.me/theorems/9780b713-8cec-404f-806c-e7b786d395bc
-- title:
--   BDL26 Countable Embedding Experiment: all Finite Success density
-- statement:
--   Domain-label counting survives arbitrary collapsed images and duplicate checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L75-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L75-L79

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_density {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ) (c : Space) :
    ((qubitHits (StagePresentation p n) (levelMap p omega n)
      (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t := by sorry
