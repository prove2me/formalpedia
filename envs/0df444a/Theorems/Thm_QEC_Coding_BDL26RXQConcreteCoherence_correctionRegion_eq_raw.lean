-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_eq_raw
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_eq_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:59:27.269198+00:00
-- url     : https://prove2.me/theorems/ef19a0ef-a7e1-461b-98cc-010d68dfce59
-- title:
--   BDL26 RXQConcrete Coherence: correction Region eq raw
-- statement:
--   Exact raw/actual region equality, not a caller coherence certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L65-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L65-L74

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_eq_raw (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) :
    (rxLq S depth i h).correctionRegion q =
      (fiberRegion (rxCorrectionOwner (state S i.val).presentation S) (Vertex.q q)).map
        (rxPhysicalQEquiv S depth i h).toEmbedding := by sorry
