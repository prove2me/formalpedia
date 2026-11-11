-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_input_syndrome_witness
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_basis_input_syndrome_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:59:06.924516+00:00
-- url     : https://prove2.me/theorems/545f02b5-5c56-45d7-b1f8-27fc945445be
-- title:
--   BDL26 RXQBlock Transport: map1 basis input syndrome witness
-- statement:
--   The nonzero lifted background also has a genuine nonzero input syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L676-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L676-L691

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.map1_basis_input_syndrome_witness (q : QCoord S i) (copy : Fin 2) :
    (errorSyndrome S depth i
      (((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val
      ((Data S depth i h).induced.zPairEquiv (incidentWitness S i q,copy)).val=1 := by sorry
