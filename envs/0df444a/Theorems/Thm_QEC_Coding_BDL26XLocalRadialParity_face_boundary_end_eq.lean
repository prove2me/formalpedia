-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_face_boundary_end_eq
-- name    : QEC.Coding.BDL26XLocalRadialParity.face_boundary_end_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:33:39.693636+00:00
-- url     : https://prove2.me/theorems/54f5539f-2b9d-42bf-9fd0-9a16752f6098
-- title:
--   BDL26 XLocal Radial Parity: face boundary end eq
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the face boundary end eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L217-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L217-L222

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.face_boundary_end_eq
    (P : TannerSquarePresentation) (x : P.X) (face : XStarFace P x) :
    xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0) =
      xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 1) := by sorry
