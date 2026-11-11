-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_exists_seed_parameters
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.exists_seed_parameters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:38:50.11617+00:00
-- url     : https://prove2.me/theorems/90845e7c-6e7b-4d70-adc7-f75285e116f0
-- title:
--   BDL26 Random Seed Embedding: exists seed parameters
-- statement:
--   Parameters are constructed independently of any later level or incoming map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L169-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L169-L177

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomSeedEmbedding.exists_seed_parameters (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) 0).presentation
        (seedPoint (perturbationOddScale p)) p.t ∧
      (∀ c, ((qubitHits (state (perturbationOddScale p) 0).presentation
        (seedPoint (perturbationOddScale p)) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t) ∧
      PhysicalGeometry (perturbationOddScale p) 0 (seedPoint (perturbationOddScale p)) p.t := by sorry
