-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_face_hit_iff
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_face_hit_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:36:12.166171+00:00
-- url     : https://prove2.me/theorems/0b46abc3-edd2-48ce-a49b-d04d20fc310a
-- title:
--   BDL26 Random Seed Embedding: seed face hit iff
-- statement:
--   The BDL26 Random Seed Embedding construction uses the seed face hit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L44-L49

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_face_hit_iff (S : OddScale) (f : (state S 0).presentation.Face)
    (ball : Set Space) :
    (tannerFaceImage (state S 0).presentation (seedPoint S) f ∩ ball).Nonempty ↔
      (0 : Space) ∈ ball := by sorry
