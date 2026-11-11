-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_syndromeRegion_eq_raw
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.syndromeRegion_eq_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:59:21.826904+00:00
-- url     : https://prove2.me/theorems/dba5262f-0d49-4b4f-85d9-9950dd92637b
-- title:
--   BDL26 RXQConcrete Coherence: syndrome Region eq raw
-- statement:
--   The actual local Q syndrome region is the original raw Q-owner fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L77-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L77-L86

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.syndromeRegion_eq_raw (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) :
    (rxLq S depth i h).syndromeRegion q =
      (fiberRegion (rxSyndromeOwner (state S i.val).presentation S) (Vertex.q q)).map
        (physicalZEquiv S depth i h).toEmbedding := by sorry
