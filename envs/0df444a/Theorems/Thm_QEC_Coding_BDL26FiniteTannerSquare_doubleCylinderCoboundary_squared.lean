-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderCoboundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:01.800212+00:00
-- url     : https://prove2.me/theorems/a7821dad-7688-48c6-8cf0-cea9bfa036ed
-- title:
--   BDL26 Finite Tanner Square: double Cylinder Coboundary squared
-- statement:
--   The constructed cylinder coboundary also squares to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2586-L2593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2586-L2593

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

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderCoboundary_squared
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (doubleCylinderCoboundary1 P x S).comp
      (doubleCylinderCoboundary0 P x S) = 0 := by sorry
