-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_source_even_geometry_ae
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.source_even_geometry_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:49:13.076201+00:00
-- url     : https://prove2.me/theorems/10e1fb32-29e4-4c70-b5d7-f68011acb3a7
-- title:
--   BDL26 Finite Embedding Experiment: source even geometry ae
-- statement:
--   Source-even levels include zero and keep the same parameters before `k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L158-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L158-L164

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.source_even_geometry_ae {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    ∀ᵐ z ∂experimentLaw p (2*k), z ∈ finiteSuccess p (2*k) ∧
      PhysicalGeometry (perturbationOddScale p) (2*k) (evaluate p (2*k) z) p.t := by sorry
