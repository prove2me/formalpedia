-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_finite_basis_classification
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.finite_basis_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:18:29.898203+00:00
-- url     : https://prove2.me/theorems/44cb2921-f4cf-458e-9c8a-575b70d67151
-- title:
--   BDL26 RXQConcrete Coherence: finite basis classification
-- statement:
--   Nontrivial finite data on every actual RX level and every scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L467-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L467-L482

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.finite_basis_classification (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    (let p := (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val
     p ∈ (rxLq S depth i h).correctionRegion q ∧
       parent S (i.val+1) (Vertex.q p)=some (Vertex.q q)) ∧
    ((rxStepOutput_ownerLabels S depth i h (basisInput S depth i q)).label
      (qComponentIndex S depth i h (basisInput S depth i q) q)).owner=some (Vertex.q q) ∧
    basisImage S depth i q≠0 ∧
    (∀ copy : Fin 2, basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv
      (BDL26RXQBlockTransport.incidentWitness S i q,copy)).val=1) ∧
    parent S (i.val+1) (Vertex.z (connector S depth i h q))=none ∧
    basisImage S depth i q (connector S depth i h q)=0 := by sorry
