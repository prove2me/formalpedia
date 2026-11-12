-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_successorKernel_apply
-- name    : QEC.Coding.BDL26RandomPerturbation.successorKernel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:58:02.650575+00:00
-- url     : https://prove2.me/theorems/b70811fa-870b-4baf-83ac-adda53b37907
-- title:
--   BDL26 Random Perturbation: successor Kernel apply
-- statement:
--   Every input, valid or not, has the exact original pushforward measure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L179-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L179-L184

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

theorem QEC.Coding.BDL26RandomPerturbation.successorKernel_apply {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space) :
    successorKernel p n J = (physicalTableLaw p n).map (physicalSuccessorOutput p n J) := by sorry
