-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_pair_witness
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_basis_pair_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:08:05.780114+00:00
-- url     : https://prove2.me/theorems/c3ffb915-95a1-456f-b2a0-b78a1b895480
-- title:
--   BDL26 RXQBlock Transport: map1 basis pair witness
-- statement:
--   The BDL26 RXQBlock Transport construction uses the map1 basis pair witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L667-L673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L667-L673

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

theorem QEC.Coding.BDL26RXQBlockTransport.map1_basis_pair_witness (q : QCoord S i) (a : Upper S depth i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val
      ((Data S depth i h).induced.zPairEquiv (incidentWitness S i q,copy)).val=1 := by sorry
