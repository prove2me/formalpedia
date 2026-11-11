-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_checks_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.physical_successor_checks_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:01:55.347482+00:00
-- url     : https://prove2.me/theorems/5e3e7574-d204-4b03-90fa-100045493451
-- title:
--   BDL26 Random Perturbation: physical successor checks ae
-- statement:
--   The BDL26 Random Perturbation construction uses the physical successor checks ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L230-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L230-L243

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
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

theorem QEC.Coding.BDL26RandomPerturbation.physical_successor_checks_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, ∀ j : Sum (ZLabel (perturbationOddScale p) (n+1))
      (XLabel (perturbationOddScale p) (n+1)),
      (∀ r ∈ checkSupport (perturbationOddScale p) (n+1) j,
        dist (physicalSuccessorOutput p n J T (.q r))
          (checkCenter _ _ (physicalSuccessorOutput p n J T) j) ≤ 1) ∧
      (∀ r ∈ checkSupport (perturbationOddScale p) (n+1) j,
        ∀ s ∈ checkSupport (perturbationOddScale p) (n+1) j,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 2) ∧
      (checkSupport (perturbationOddScale p) (n+1) j).card ≤ 7 := by sorry
