-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_physicalZ_parent
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.physicalZ_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:34:29.289804+00:00
-- url     : https://prove2.me/theorems/8703e836-8a6f-4a29-b677-4738c0518e7f
-- title:
--   BDL26 RXQConcrete Coherence: physical Z parent
-- statement:
--   The corresponding statement for the original selected syndrome carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L113-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L113-L119

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.physicalZ_parent (h : i.val%2=0)
    (r : RX2 (state S i.val).presentation S) :
    parent S (i.val+1) (Vertex.z (physicalZEquiv S depth i h r)) =
      rxParent (state S i.val).presentation S (Vertex.z r) := by sorry
