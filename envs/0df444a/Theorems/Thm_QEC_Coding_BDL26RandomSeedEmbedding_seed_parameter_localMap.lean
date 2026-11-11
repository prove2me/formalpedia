-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_localMap
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_parameter_localMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:17:58.618082+00:00
-- url     : https://prove2.me/theorems/98386c4d-419a-4a8e-aa85-088dd912273a
-- title:
--   BDL26 Random Seed Embedding: seed parameter local Map
-- statement:
--   The seed fits the same arbitrary parameters and their same odd scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L93-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L93-L96

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_parameter_localMap {L : ℝ} (p : GeometricParameters L) :
    IsBoundedDensityLocalMap (state (perturbationOddScale p) 0).presentation
      (seedPoint (perturbationOddScale p)) p.t := by sorry
