-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_pair
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.basisImage_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:34:37.680262+00:00
-- url     : https://prove2.me/theorems/b40433ce-e122-4bda-862d-12992a1443c5
-- title:
--   BDL26 RXQConcrete Coherence: basis Image pair
-- statement:
--   The BDL26 RXQConcrete Coherence construction uses the basis Image pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L307-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L307-L313

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.basisImage_pair (h : i.val%2=0) (q : (state S i.val).presentation.Q)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv (z,copy)).val =
      if (state S i.val).presentation.qz q z=true then 1 else 0 := by sorry
