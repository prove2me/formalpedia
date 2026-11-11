-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_successorLaw_good_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.successorLaw_good_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:57:52.440442+00:00
-- url     : https://prove2.me/theorems/b0858f1d-b18f-4aca-b290-a88324457d2b
-- title:
--   BDL26 Random Perturbation: successor Law good ae
-- statement:
--   The BDL26 Random Perturbation construction uses the successor Law good ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L240-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L240-L250

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26RandomPerturbation.successorLaw_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ J ∂μ, IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ J' ∂(successorKernel p n) ∘ₘ μ,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation J' p.t := by sorry
