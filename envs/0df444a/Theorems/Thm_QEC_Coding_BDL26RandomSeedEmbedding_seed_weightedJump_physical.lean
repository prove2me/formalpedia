-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_weightedJump_physical
-- name    : QEC.Coding.BDL26RandomSeedEmbedding.seed_weightedJump_physical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:39:31.81843+00:00
-- url     : https://prove2.me/theorems/54468049-fcbd-418d-9137-ef7bf78c505e
-- title:
--   BDL26 Random Seed Embedding: seed weighted Jump physical
-- statement:
--   No rate hypothesis is needed for the actual square-root-rate jump support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L153-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SeedEmbedding.lean#L153-L166

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

theorem QEC.Coding.BDL26RandomSeedEmbedding.seed_weightedJump_physical (S : OddScale)
    (rate : BDL26CSSDaviesLocality.CouplingIndex S 0 → BDL26CSSDaviesLocality.Frequency S 0 → ℝ)
    (q : Physical S 0) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S 0) :
    (BDL26CSSDaviesLocality.subsystem S 0 q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S 0) (BDL26CSSDaviesLocality.hamiltonian_symmetric S 0)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S 0 =>
          BDL26CSSDaviesLocality.coupling S 0 qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ r ∈ region S 0 q, dist (seedPoint S (.q r)) (seedPoint S (.q q)) = 0) ∧
    (∀ r ∈ region S 0 q, ∀ s ∈ region S 0 q,
      dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0) ∧
    (BDL26CSSDaviesLocality.subsystem S 0 q).selected.card ≤ 5 := by sorry
