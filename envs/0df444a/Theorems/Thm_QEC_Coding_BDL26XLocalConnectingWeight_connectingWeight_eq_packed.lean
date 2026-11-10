-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_eq_packed
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_eq_packed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:24:48.217727+00:00
-- url     : https://prove2.me/theorems/e7714dea-7710-4e91-8348-7fb154222e90
-- title:
--   BDL26 XLocal Connecting Weight: connecting Weight eq packed
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the connecting Weight eq packed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L39-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L39-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_eq_packed
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f : Word (ZMod 2) (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S f = HammingWeight (fun d => f (outputEdge P A x S d)) := by sorry
