-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_check_radius_zero
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_check_radius_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:37:43.349907+00:00
-- url     : https://prove2.me/theorems/4e51bf3d-3701-49c1-8618-88342650f7b8
-- title:
--   BDL26 Random Seed Embedding: seed check radius zero
-- statement:
--   The sharper seed geometry holds for all labels, even outside a selected check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L116-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L116-L118

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_check_radius_zero (S : OddScale) (j : Sum (ZLabel S 0) (XLabel S 0))
    (r : Physical S 0) : dist (seedPoint S (.q r)) (checkCenter S 0 (seedPoint S) j) = 0 := by sorry
