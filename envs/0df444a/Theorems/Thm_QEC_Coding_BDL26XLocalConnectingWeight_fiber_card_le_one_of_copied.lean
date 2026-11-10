-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_fiber_card_le_one_of_copied
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.fiber_card_le_one_of_copied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:25:05.259566+00:00
-- url     : https://prove2.me/theorems/9c61ef24-d76e-476c-bb80-ca694dc1acdb
-- title:
--   BDL26 XLocal Connecting Weight: fiber card le one of copied
-- statement:
--   A copied original boundary segment occurs in at most one output block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L103-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L103-L126

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.fiber_card_le_one_of_copied
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (q : P.Q) (he : copiedQ P x S e = some q) :
    Fintype.card (Fiber P A x S e) ≤ 1 := by sorry
