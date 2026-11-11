-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_not_q_parent
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.basisImage_not_q_parent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:19:52.093465+00:00
-- url     : https://prove2.me/theorems/99d2a264-354a-4e7c-97b8-f86bf75e3ef0
-- title:
--   BDL26 RXQConcrete Coherence: basis Image not q parent
-- statement:
--   This is a Z-parent image, and cannot be claimed to be a single Q fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L424-L433
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L424-L433

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.basisImage_not_q_parent (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    ∃ p ∈ hammingSupport (basisImage S depth i q),
      parent S (i.val+1) (Vertex.z p)≠some (Vertex.q q) := by sorry
