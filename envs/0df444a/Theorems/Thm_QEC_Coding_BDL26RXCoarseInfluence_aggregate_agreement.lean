-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_aggregate_agreement
-- name    : QEC.Coding.BDL26RXCoarseInfluence.aggregate_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:07:07.821092+00:00
-- url     : https://prove2.me/theorems/ad91cd21-245d-4f81-912b-e2b1504ff7c0
-- title:
--   BDL26 RXCoarse Influence: aggregate agreement
-- statement:
--   Derive equality of the finite actual xi sums from each contributing region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L112-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L112-L133

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.aggregate_agreement (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) :
    rxXiSignal (rxData S depth i h) sigma.val ((rxData S depth i h).coarseCenter z) 2 =
      rxXiSignal (rxData S depth i h) (sigmaPlus S depth i sigma q).val
        ((rxData S depth i h).coarseCenter z) 2 := by sorry
