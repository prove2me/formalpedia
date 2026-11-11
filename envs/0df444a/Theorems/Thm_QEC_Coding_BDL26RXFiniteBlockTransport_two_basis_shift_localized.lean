-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_two_basis_shift_localized
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.two_basis_shift_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:20:52.075086+00:00
-- url     : https://prove2.me/theorems/21202c4a-2c1d-41c7-ba84-acdafe0ffe32
-- title:
--   BDL26 RXFinite Block Transport: two basis shift localized
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the two basis shift localized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L740-L751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L740-L751

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.two_basis_shift_localized (q0 q1 : QCoord S i) (a : Upper S depth i) :
    Localized S depth i h ∅ {q0,q1} a
      (a+((indexedDecoderData S depth).selectedMap i).map1
        (canonicalBasisWord q0+canonicalBasisWord q1)) := by sorry
