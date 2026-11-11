-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seedPoint_eq_zero
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seedPoint_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:17:46.15359+00:00
-- url     : https://prove2.me/theorems/c1fdb7e0-b9dd-4f56-88e1-3491212661e0
-- title:
--   BDL26 Random Seed Embedding: seed Point eq zero
-- statement:
--   The BDL26 Random Seed Embedding construction uses the seed Point eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L23-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L23-L24

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seedPoint_eq_zero (S : OddScale) (v : Vertex (state S 0).presentation) :
    seedPoint S v = 0 := by sorry

attribute [defeq] QEC.Coding.BDL26RandomSeedEmbedding.seedPoint_eq_zero
