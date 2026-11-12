-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_checks
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_checks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:41:30.507547+00:00
-- url     : https://prove2.me/theorems/b99cfe02-33c2-4f3a-8a6d-b9b465b099d7
-- title:
--   BDL26 Countable Embedding Experiment: all Finite Success checks
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the all Finite Success checks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L81-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L81-L91

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_checks {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ)
    (j : Sum (ZLabel (perturbationOddScale p) n) (XLabel (perturbationOddScale p) n)) :
    (∀ r ∈ checkSupport (perturbationOddScale p) n j,
      dist (levelMap p omega n (.q r))
        (checkCenter (perturbationOddScale p) n (levelMap p omega n) j) ≤ 1) ∧
    (∀ r ∈ checkSupport (perturbationOddScale p) n j,
      ∀ s ∈ checkSupport (perturbationOddScale p) n j,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 2) ∧
    (checkSupport (perturbationOddScale p) n j).card ≤ 7 := by sorry
