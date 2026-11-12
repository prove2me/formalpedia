-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_oldZ_pair_distinct
-- name    : QEC.Coding.BDL26RXQConcreteCoherence.oldZ_pair_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:17:54.731688+00:00
-- url     : https://prove2.me/theorems/06fe1db8-d024-4487-847c-4059afa3a594
-- title:
--   BDL26 RXQConcrete Coherence: old Z pair distinct
-- statement:
--   Both selected old-Z copies are retained as distinct actual coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L379-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean#L379-L384

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

theorem QEC.Coding.BDL26RXQConcreteCoherence.oldZ_pair_distinct (h : i.val%2=0) (z : (state S i.val).presentation.Z) :
    ((rxData S depth i h).induced.zPairEquiv (z,0)).val ≠
      ((rxData S depth i h).induced.zPairEquiv (z,1)).val := by sorry
