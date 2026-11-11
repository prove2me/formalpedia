-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_mem_iff
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.basisImage_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:34:30.952722+00:00
-- url     : https://prove2.me/theorems/167b5ca9-fceb-421d-b5ba-ec562f8b857e
-- title:
--   BDL26 RXQConcrete Coherence: basis Image mem iff
-- statement:
--   Exhaustive support; no upper syndrome coordinates are discarded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L323-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L323-L346

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.basisImage_mem_iff (h : i.val%2=0) (q : (state S i.val).presentation.Q)
    (p : FamilyZ S depth i.succ) :
    p ∈ hammingSupport (basisImage S depth i q) ↔
      ∃ (z : (state S i.val).presentation.Z) (copy : Fin 2),
        (state S i.val).presentation.qz q z=true ∧
        ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=p := by sorry
