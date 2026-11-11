-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_q_assembly_snapshot
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.q_assembly_snapshot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:01:33.508097+00:00
-- url     : https://prove2.me/theorems/69094dc4-b245-4a23-a93b-1cb284cf2a51
-- title:
--   BDL26 RXQConcrete Coherence: q assembly snapshot
-- statement:
--   Exact #815 local piece, owner label and unchanged stored supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L247-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L247-L263

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.q_assembly_snapshot (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    let j := qComponentIndex S depth i h sigma q
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).owner=some (Vertex.q q) ∧
    (rxStepOutput S depth i h sigma).componentAt j=
      cqComponentTotal (rxData S depth i h) sigma.val q ∧
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).correctionSupport=
      (rxStepOutput S depth i h sigma).componentSupportAt j ∧
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).coboundarySupport=
      hammingSupport ((rxStepOutput S depth i h sigma).componentCoboundaryAt j) := by sorry
