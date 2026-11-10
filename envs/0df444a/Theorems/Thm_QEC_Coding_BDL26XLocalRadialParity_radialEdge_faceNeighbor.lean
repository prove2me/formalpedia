-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialEdge_faceNeighbor
-- name    : QEC.Coding.BDL26XLocalRadialParity.radialEdge_faceNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:07.179004+00:00
-- url     : https://prove2.me/theorems/b0a106e1-7862-40f1-adcd-3e39359d564e
-- title:
--   BDL26 XLocal Radial Parity: radial Edge face Neighbor
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the radial Edge face Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L200-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L200-L207

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.radialEdge_faceNeighbor
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (face : XStarFace P x) (side : Two) :
    radialEdge P A x (faceNeighbor P x face side) = xStarFaceXQEdge P x face side := by sorry
