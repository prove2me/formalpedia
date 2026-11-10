-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single_le_of_vertical
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single_le_of_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:24:02.032623+00:00
-- url     : https://prove2.me/theorems/9c772b0c-4d3e-4199-afe4-0a7c9c1106c2
-- title:
--   BDL26 XLocal Connecting Weight: connecting Weight single le of vertical
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the connecting Weight single le of vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L198-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L198-L206

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single_le_of_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (z : P.Z) (he : verticalZ P x S e = some z) (b : ZMod 2) :
    connectingWeight P A x S (Pi.single e b) ≤ 2 * bitWeight b := by sorry
