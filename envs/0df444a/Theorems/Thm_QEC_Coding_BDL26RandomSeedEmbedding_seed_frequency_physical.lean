-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_frequency_physical
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_frequency_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:37:48.287692+00:00
-- url     : https://prove2.me/theorems/82ed5ba0-9df1-4be4-b439-bd18769235cb
-- title:
--   BDL26 Random Seed Embedding: seed frequency physical
-- statement:
--   All real frequencies of the actual full Hamiltonian have zero-diameter seed support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L139-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L139-L150

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_frequency_physical (S : OddScale) (q : Physical S 0)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem S 0 q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S 0) (BDL26CSSDaviesLocality.hamiltonian_symmetric S 0)
        (BDL26CSSDaviesLocality.coupling S 0 q a) ω) ∧
    (∀ r ∈ region S 0 q, dist (seedPoint S (.q r)) (seedPoint S (.q q)) = 0) ∧
    (∀ r ∈ region S 0 q, ∀ s ∈ region S 0 q,
      dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0) ∧
    (BDL26CSSDaviesLocality.subsystem S 0 q).selected.card ≤ 5 := by sorry
