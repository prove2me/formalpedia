-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_oldZ_pair_parent
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.oldZ_pair_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:35:28.166204+00:00
-- url     : https://prove2.me/theorems/5e573832-beed-495d-b4e6-f8326aba2990
-- title:
--   BDL26 RXQConcrete Coherence: old Z pair parent
-- statement:
--   Every actual selected old-Z chart has its Z parent, for BOTH copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L216-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L216-L231

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.oldZ_pair_parent (h : i.val%2=0)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    parent S (i.val+1)
      (Vertex.z ((rxData S depth i h).induced.zPairEquiv (z,copy)).val)=some (Vertex.z z) := by sorry
