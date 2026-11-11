-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_parent_iff
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_parent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:35:44.851065+00:00
-- url     : https://prove2.me/theorems/f17a4d21-2017-4847-998b-1b992e2dbded
-- title:
--   BDL26 RXQConcrete Coherence: correction Region parent iff
-- statement:
--   The concrete Q correction fibre is exactly the real Q-parent fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L153-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L153-L167

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_parent_iff (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ) :
    p ∈ (rxLq S depth i h).correctionRegion q ↔
      parent S (i.val+1) (Vertex.q p)=some (Vertex.q q) := by sorry
