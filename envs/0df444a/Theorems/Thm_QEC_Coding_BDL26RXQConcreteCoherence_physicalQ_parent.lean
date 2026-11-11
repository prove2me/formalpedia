-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_physicalQ_parent
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.physicalQ_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:00:14.806013+00:00
-- url     : https://prove2.me/theorems/654b37b4-e756-4148-98fa-a5f198bac6d6
-- title:
--   BDL26 RXQConcrete Coherence: physical Q parent
-- statement:
--   All raw Q-coordinate tags compute the existing adjacent graph parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L104-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L104-L110

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.physicalQ_parent (h : i.val%2=0)
    (r : RX1 (state S i.val).presentation S) :
    parent S (i.val+1) (Vertex.q (rxPhysicalQEquiv S depth i h r)) =
      rxParent (state S i.val).presentation S (Vertex.q r) := by sorry
