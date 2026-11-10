-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single_eq_zero_of_other
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single_eq_zero_of_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:15:29.705515+00:00
-- url     : https://prove2.me/theorems/458b2481-45ac-494f-b0ae-e63d9ce34e26
-- title:
--   BDL26 XLocal Connecting Weight: connecting Weight single eq zero of other
-- statement:
--   All other cylinder edge tags have zero connecting cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L209-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L209-L222

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single_eq_zero_of_other
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (hc : copiedQ P x S e = none) (hv : verticalZ P x S e = none)
    (b : ZMod 2) : connectingWeight P A x S (Pi.single e b) = 0 := by sorry
