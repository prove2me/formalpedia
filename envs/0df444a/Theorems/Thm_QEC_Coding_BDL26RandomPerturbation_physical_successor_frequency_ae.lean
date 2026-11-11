-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_frequency_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.physical_successor_frequency_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:03:45.500497+00:00
-- url     : https://prove2.me/theorems/400c378f-2ef6-4923-ba95-a362b9ceb5c5
-- title:
--   BDL26 Random Perturbation: physical successor frequency ae
-- statement:
--   The BDL26 Random Perturbation construction uses the physical successor frequency ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L258-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L258-L274

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

theorem QEC.Coding.BDL26RandomPerturbation.physical_successor_frequency_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t)
    (q : Physical (perturbationOddScale p) (n+1)) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    ∀ᵐ T ∂physicalTableLaw p n,
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).OperatorSupportedOnRegister
        (actualFrequency (hamiltonian (perturbationOddScale p) (n+1))
          (BDL26CSSDaviesLocality.hamiltonian_symmetric _ _)
          (BDL26CSSDaviesLocality.coupling _ _ q a) ω) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q q)) ≤ 2) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        ∀ s ∈ region (perturbationOddScale p) (n+1) q,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 4) ∧
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).selected.card ≤ 50 := by sorry
