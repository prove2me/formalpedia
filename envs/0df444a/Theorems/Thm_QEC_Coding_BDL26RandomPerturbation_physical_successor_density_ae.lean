-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_density_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.physical_successor_density_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:05:40.453719+00:00
-- url     : https://prove2.me/theorems/15f42543-261a-4f6c-b291-503660186ff1
-- title:
--   BDL26 Random Perturbation: physical successor density ae
-- statement:
--   The BDL26 Random Perturbation construction uses the physical successor density ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L221-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L221-L228

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

theorem QEC.Coding.BDL26RandomPerturbation.physical_successor_density_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, ∀ c,
      ((qubitHits (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n J T) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t := by sorry
