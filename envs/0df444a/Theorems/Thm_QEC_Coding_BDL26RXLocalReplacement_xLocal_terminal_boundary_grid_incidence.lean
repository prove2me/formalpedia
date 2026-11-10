-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_terminal_boundary_grid_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_terminal_boundary_grid_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:22.900428+00:00
-- url     : https://prove2.me/theorems/f701751f-d959-42d5-b0ef-6c7f7446dc3a
-- title:
--   BDL26 RXLocal Replacement: x Local terminal boundary grid incidence
-- statement:
--   Each terminal boundary segment has one adjacent terminal grid cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L769-L802
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L769-L802

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_terminal_boundary_grid_incidence
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (side : Two)
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S
      (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (xLocalLast S)).val target =
      if target = (face, xLocalGridRoot S) then 1 else 0 := by sorry
