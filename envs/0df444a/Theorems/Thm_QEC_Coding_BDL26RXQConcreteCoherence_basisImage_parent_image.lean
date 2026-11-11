-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_parent_image
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.basisImage_parent_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:17:31.917808+00:00
-- url     : https://prove2.me/theorems/57366ff1-0887-4af9-92bd-38b4ef57495d
-- title:
--   BDL26 RXQConcrete Coherence: basis Image parent image
-- statement:
--   Exact parent image of the full selected syndrome support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L387-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L387-L406

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.basisImage_parent_image (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    (hammingSupport (basisImage S depth i q)).image
      (fun p => parent S (i.val+1) (Vertex.z p)) =
      (BDL26RXQBlockTransport.incidentZ S i q).image (fun z => some (Vertex.z z)) := by sorry
