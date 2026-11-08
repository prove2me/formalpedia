-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderRectangleBoundaryEdge_injective
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderRectangleBoundaryEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:30:09.918201+00:00
-- url     : https://prove2.me/theorems/944345b3-44f0-47b5-b1fd-9ad0742151c8
-- title:
--   BDL26 Finite Tanner Square: double Cylinder Rectangle Boundary Edge injective
-- statement:
--   The two end-copy and two vertical rectangle edges retain distinct slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2391-L2400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2391-L2400

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

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderRectangleBoundaryEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    Function.Injective
      (doubleCylinderRectangleBoundaryEdge P x S rectangle) := by sorry
