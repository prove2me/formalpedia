-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_q_chart_coherent
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.q_chart_coherent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:03:31.190373+00:00
-- url     : https://prove2.me/theorems/02207c92-cbb9-47ca-a8ff-27e2261d0a4a
-- title:
--   BDL26 RXQConcrete Coherence: q chart coherent
-- statement:
--   Actual cylinder charts retain their raw tag, owner and genuine parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L178-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L178-L190

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.q_chart_coherent (h : i.val%2=0)
    (q : (state S i.val).presentation.Q)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    (rxQVertexEquiv S depth i h q v).val =
      rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) ∧
    vertexEquiv (state S i.val).presentation
      (correctionOwnerAt S depth i h (rxQVertexEquiv S depth i h q v).val)=Vertex.q q ∧
    parent S (i.val+1) (Vertex.q (rxQVertexEquiv S depth i h q v).val)=some (Vertex.q q) := by sorry
