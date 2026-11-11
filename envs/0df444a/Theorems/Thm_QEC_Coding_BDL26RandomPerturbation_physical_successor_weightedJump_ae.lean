-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_weightedJump_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.physical_successor_weightedJump_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:07:28.613465+00:00
-- url     : https://prove2.me/theorems/74bb84bf-4d36-4f44-8bf6-aaa6f6372866
-- title:
--   BDL26 Random Perturbation: physical successor weighted Jump ae
-- statement:
--   The BDL26 Random Perturbation construction uses the physical successor weighted Jump ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L276-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L276-L296

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory
variable {L : ℝ}

theorem QEC.Coding.BDL26RandomPerturbation.physical_successor_weightedJump_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t)
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) (n+1) →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) (n+1) → ℝ)
    (q : Physical (perturbationOddScale p) (n+1)) (a : CSSDaviesLocality.Axis)
    (ω : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) (n+1)) :
    ∀ᵐ T ∂physicalTableLaw p n,
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).OperatorSupportedOnRegister
        (hamiltonianJump (hamiltonian (perturbationOddScale p) (n+1))
          (BDL26CSSDaviesLocality.hamiltonian_symmetric _ _)
          (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) (n+1) =>
            BDL26CSSDaviesLocality.coupling _ _ qa.1 qa.2) rate ((q,a),ω)) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q q)) ≤ 2) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        ∀ s ∈ region (perturbationOddScale p) (n+1) q,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 4) ∧
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).selected.card ≤ 50 := by sorry
