-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorOutput_rz
-- name    : QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_rz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:38:56.429669+00:00
-- url     : https://prove2.me/theorems/d696f582-6847-4bbc-8e13-6ed0ecc22028
-- title:
--   BDL26 Random Perturbation: physical Successor Output rz
-- statement:
--   The BDL26 Random Perturbation construction uses the physical Successor Output rz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L155-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L155-L162

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

theorem QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_rz (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (h : ¬ n % 2 = 0) : physicalSuccessorOutput p n J T = fun v =>
      rzVertexPoint _ (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
        (perturbationOddScale p) (perturbationEmbeddingOutput _ J p T)
        (nextRZVertex _ n (state (perturbationOddScale p) n) h v) := by sorry
