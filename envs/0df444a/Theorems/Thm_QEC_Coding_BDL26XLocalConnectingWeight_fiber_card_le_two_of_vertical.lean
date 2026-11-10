-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_fiber_card_le_two_of_vertical
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.fiber_card_le_two_of_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:24:15.916995+00:00
-- url     : https://prove2.me/theorems/27a741e2-90de-4089-8763-25ab7937cd34
-- title:
--   BDL26 XLocal Connecting Weight: fiber card le two of vertical
-- statement:
--   A vertical old-Z corner can meet only the two corners of its unique face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L174-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L174-L196

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.fiber_card_le_two_of_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (z : P.Z) (he : verticalZ P x S e = some z) :
    Fintype.card (Fiber P A x S e) ≤ 2 := by sorry
