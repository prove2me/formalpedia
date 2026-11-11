-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_face_count
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_face_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:35:59.618861+00:00
-- url     : https://prove2.me/theorems/6299847c-b2fc-4165-b593-943557fec45d
-- title:
--   BDL26 Random Seed Embedding: seed face count
-- statement:
--   Domain faces are retained even though the image consists of one point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L52-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L52-L59

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_face_count (S : OddScale) (c : Space) :
    (familyHits (tannerFaceImage (state S 0).presentation (seedPoint S))
      (Metric.closedBall c 1)).card =
        if (0 : Space) ∈ Metric.closedBall c 1 then 4 else 0 := by sorry
