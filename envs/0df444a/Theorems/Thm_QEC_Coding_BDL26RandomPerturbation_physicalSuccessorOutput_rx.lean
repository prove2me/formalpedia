-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorOutput_rx
-- name    : QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_rx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:39:31.164797+00:00
-- url     : https://prove2.me/theorems/c7c1350c-202b-4ca6-8eb0-b918a9011f12
-- title:
--   BDL26 Random Perturbation: physical Successor Output rx
-- statement:
--   The BDL26 Random Perturbation construction uses the physical Successor Output rx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L147-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L147-L153

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

theorem QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_rx (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (h : n % 2 = 0) : physicalSuccessorOutput p n J T = fun v =>
      rxVertexPoint _ (perturbationOddScale p) (perturbationEmbeddingOutput _ J p T)
        (nextRXVertex _ n (state (perturbationOddScale p) n) h v) := by sorry
