-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_check_center_zero
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_check_center_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:37:01.445928+00:00
-- url     : https://prove2.me/theorems/5d039603-3334-45e8-8f8a-d9bf62fdc112
-- title:
--   BDL26 Random Seed Embedding: seed check center zero
-- statement:
--   The BDL26 Random Seed Embedding construction uses the seed check center zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L111-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L111-L113

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_check_center_zero (S : OddScale) (j : Sum (ZLabel S 0) (XLabel S 0)) :
    checkCenter S 0 (seedPoint S) j = 0 := by sorry
