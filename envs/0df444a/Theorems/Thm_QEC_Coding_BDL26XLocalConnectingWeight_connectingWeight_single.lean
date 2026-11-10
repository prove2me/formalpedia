-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:15:10.393914+00:00
-- url     : https://prove2.me/theorems/7a582f61-9ceb-4795-88e1-a74ef95b3c65
-- title:
--   BDL26 XLocal Connecting Weight: connecting Weight single
-- statement:
--   Exact basis cost, with no assumed support or multiplicity bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L49-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L49-L66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) (b : ZMod 2) :
    connectingWeight P A x S (Pi.single e b) =
      bitWeight b * Fintype.card (Fiber P A x S e) := by sorry
