-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_physical_success
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_physical_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:56:58.148294+00:00
-- url     : https://prove2.me/theorems/8a8fc54e-56ef-4a21-a10f-64cc6637e878
-- title:
--   BDL26 Random Perturbation: measurable Set physical success
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set physical success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L209-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EmbeddingKernel.lean#L209-L220

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

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_physical_success {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet {z :
      (Vertex (state (perturbationOddScale p) n).presentation → Space) ×
        Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space) |
      Halts (eventSupport (state (perturbationOddScale p) n).presentation z.1 (anchorRadius p.m))
        (eventBad (state (perturbationOddScale p) n).presentation z.1
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) z.2 ∧
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n z.1 z.2) p.t} := by sorry
