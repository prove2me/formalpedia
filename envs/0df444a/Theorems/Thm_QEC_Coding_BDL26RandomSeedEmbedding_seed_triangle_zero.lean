-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_triangle_zero
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_triangle_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:33:54.529287+00:00
-- url     : https://prove2.me/theorems/febe6825-5f5c-408f-b67f-94b526cc93fd
-- title:
--   BDL26 Random Seed Embedding: seed triangle zero
-- statement:
--   Both actual affine charts vanish for every affine parameter, without a domain restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L35-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L35-L38

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_triangle_zero (S : OddScale) (f : (state S 0).presentation.Face)
    (side : Two) (a b : ℝ) :
    tannerTrianglePoint (state S 0).presentation (seedPoint S) f side a b = 0 := by sorry
