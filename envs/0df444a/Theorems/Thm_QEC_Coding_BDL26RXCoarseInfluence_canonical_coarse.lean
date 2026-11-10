-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_canonical_coarse
-- name    : QEC.Coding.BDL26RXCoarseInfluence.canonical_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:09:50.981229+00:00
-- url     : https://prove2.me/theorems/e0aa819a-e45d-477b-8490-cef8e06bb4e9
-- title:
--   BDL26 RXCoarse Influence: canonical coarse
-- statement:
--   Canonical selected-run coarse output, without replacing the decoder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L136-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L136-L139

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.canonical_coarse (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).coarse.val = rxCoarseWord (rxData S depth i h) sigma.val := by sorry
