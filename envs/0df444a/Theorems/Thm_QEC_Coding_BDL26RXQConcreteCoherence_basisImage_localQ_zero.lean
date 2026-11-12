-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_localQ_zero
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.basisImage_localQ_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:20:38.276701+00:00
-- url     : https://prove2.me/theorems/0a44099c-5914-4d77-9339-0f05cdadeea3
-- title:
--   BDL26 RXQConcrete Coherence: basis Image local Q zero
-- statement:
--   No positive-dimensional local-Q syndrome is a native selected image coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L365-L376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L365-L376

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.basisImage_localQ_zero (h : i.val%2=0)
    (q t : (state S i.val).presentation.Q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ (rxLq S depth i h).syndromeRegion t) :
    basisImage S depth i q p=0 := by sorry
