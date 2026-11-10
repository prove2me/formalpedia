-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_horizontal_dual_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_horizontal_dual_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:25:29.065211+00:00
-- url     : https://prove2.me/theorems/8192e59e-7270-471c-8039-c48628c2ec89
-- title:
--   BDL26 RXLocal Replacement: x Local horizontal dual incidence
-- statement:
--   An interior horizontal primal edge has exactly its two adjacent grid faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L326-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L326-L346

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_horizontal_dual_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i : Fin S.half) (j : Fin (S.half - 1))
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (f, i, j))) target =
      (if target = (f, i, stripStart S.half j) then 1 else 0) +
        (if target = (f, i, stripEnd S.half j) then 1 else 0) := by sorry
