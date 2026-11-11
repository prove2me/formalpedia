-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_halts_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.physical_successor_halts_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:01:46.073201+00:00
-- url     : https://prove2.me/theorems/f9ba2eab-36b3-44e6-9e8b-c14f055f054c
-- title:
--   BDL26 Random Perturbation: physical successor halts ae
-- statement:
--   The BDL26 Random Perturbation construction uses the physical successor halts ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L211-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L211-L219

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

theorem QEC.Coding.BDL26RandomPerturbation.physical_successor_halts_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n,
      Halts (eventSupport (state (perturbationOddScale p) n).presentation J (anchorRadius p.m))
        (eventBad (state (perturbationOddScale p) n).presentation J
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T := by sorry
