-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_chart_iff
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_chart_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:01:09.460393+00:00
-- url     : https://prove2.me/theorems/33f6a27c-b6a9-4f6f-813e-18d52c0c98bd
-- title:
--   BDL26 RXQConcrete Coherence: correction Region chart iff
-- statement:
--   Literal raw owner membership on every physical chart coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L137-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L137-L150

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_chart_iff (h : i.val%2=0)
    (q : (state S i.val).presentation.Q)
    (r : RX1 (state S i.val).presentation S) :
    rxPhysicalQEquiv S depth i h r ∈ (rxLq S depth i h).correctionRegion q ↔
      rxCorrectionOwner (state S i.val).presentation S r=Vertex.q q := by sorry
