-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_distance_zero
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_physical_distance_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:22:25.748364+00:00
-- url     : https://prove2.me/theorems/441b5443-6501-4f9c-b924-b55d586e8a14
-- title:
--   BDL26 Random Seed Embedding: seed physical distance zero
-- statement:
--   The BDL26 Random Seed Embedding construction uses the seed physical distance zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L120-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L120-L122

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_physical_distance_zero (S : OddScale) (r s : Physical S 0) :
    dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0 := by sorry
