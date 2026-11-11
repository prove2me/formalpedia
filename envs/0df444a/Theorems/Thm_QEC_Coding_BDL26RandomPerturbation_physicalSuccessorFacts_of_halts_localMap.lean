-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorFacts_of_halts_localMap
-- name    : QEC.Coding.BDL26RandomPerturbation.physicalSuccessorFacts_of_halts_localMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:56:11.493503+00:00
-- url     : https://prove2.me/theorems/874dc368-d199-423d-84d8-baa207f0c7ca
-- title:
--   BDL26 Random Perturbation: physical Successor Facts of halts local Map
-- statement:
--   Only the measurable halting-and-good-map event is needed for the full endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L197-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L197-L207

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

theorem QEC.Coding.BDL26RandomPerturbation.physicalSuccessorFacts_of_halts_localMap {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (hh : Halts (eventSupport (state (perturbationOddScale p) n).presentation J (anchorRadius p.m))
      (eventBad (state (perturbationOddScale p) n).presentation J
        (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)
    (hg : IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
      (physicalSuccessorOutput p n J T) p.t) : PhysicalSuccessorFacts p n J T := by sorry
