-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionOwner_chart
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.correctionOwner_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:58:59.322625+00:00
-- url     : https://prove2.me/theorems/1ed6c989-84a9-415b-924a-9d222f4f283b
-- title:
--   BDL26 RXQConcrete Coherence: correction Owner chart
-- statement:
--   The actual owner on the physical Q chart is the original raw owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L89-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L89-L101

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.correctionOwner_chart (h : i.val%2=0)
    (r : RX1 (state S i.val).presentation S) :
    vertexEquiv (state S i.val).presentation
      (correctionOwnerAt S depth i h (rxPhysicalQEquiv S depth i h r)) =
        rxCorrectionOwner (state S i.val).presentation S r := by sorry
