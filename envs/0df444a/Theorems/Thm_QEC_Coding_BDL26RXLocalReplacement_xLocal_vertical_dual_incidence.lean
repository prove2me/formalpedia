-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_vertical_dual_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_vertical_dual_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:25:49.890952+00:00
-- url     : https://prove2.me/theorems/c2a2f7e4-16f3-45c9-9876-5d1b226e33da
-- title:
--   BDL26 RXLocal Replacement: x Local vertical dual incidence
-- statement:
--   An interior vertical primal edge has exactly its two adjacent grid faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L349-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L349-L369

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_vertical_dual_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i : Fin (S.half - 1)) (j : Fin S.half)
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inr (f, i, j))) target =
      (if target = (f, stripStart S.half i, j) then 1 else 0) +
        (if target = (f, stripEnd S.half i, j) then 1 else 0) := by sorry
