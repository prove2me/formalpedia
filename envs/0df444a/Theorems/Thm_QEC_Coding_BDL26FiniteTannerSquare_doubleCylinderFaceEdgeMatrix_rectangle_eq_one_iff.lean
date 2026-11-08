-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:31:17.590544+00:00
-- url     : https://prove2.me/theorems/ea440fc9-de6f-46f2-aebe-b6ae0a258ce7
-- title:
--   BDL26 Finite Tanner Square: double Cylinder Face Edge Matrix rectangle eq one iff
-- statement:
--   Rectangle matrix incidence is exactly membership in the four explicit
--   boundary slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2404-L2453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2404-L2453

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S edge (Sum.inr rectangle) = 1 ↔
      ∃ slot : Two × Two,
        doubleCylinderRectangleBoundaryEdge P x S rectangle slot = edge := by sorry
