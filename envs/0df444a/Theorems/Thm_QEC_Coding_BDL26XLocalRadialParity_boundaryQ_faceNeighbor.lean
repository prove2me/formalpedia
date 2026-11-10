-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_boundaryQ_faceNeighbor
-- name    : QEC.Coding.BDL26XLocalRadialParity.boundaryQ_faceNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:34:17.49466+00:00
-- url     : https://prove2.me/theorems/fdd65556-3dce-4fdd-a42d-3270df337cb0
-- title:
--   BDL26 XLocal Radial Parity: boundary Q face Neighbor
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the boundary Q face Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L209-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L209-L215

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.boundaryQ_faceNeighbor
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (face : XStarFace P x) (side : Two) :
    boundaryQ P A x (faceNeighbor P x face side) =
      xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face side) := by sorry
