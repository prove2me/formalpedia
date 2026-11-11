-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorOutput_law
-- name    : QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:57:58.078809+00:00
-- url     : https://prove2.me/theorems/ab775b06-43ba-4836-9ee5-d1dc2699e5b8
-- title:
--   BDL26 Random Perturbation: physical Successor Output law
-- statement:
--   Exact law of the literal product experiment, expressed as kernel composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L187-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L187-L194

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

theorem QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_law {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ] :
    (μ.prod (physicalTableLaw p n)).map (fun z => physicalSuccessorOutput p n z.1 z.2) =
      (successorKernel p n) ∘ₘ μ := by sorry
