-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_cellularCoboundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.cellularCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:23:29.000195+00:00
-- url     : https://prove2.me/theorems/a9d6b28e-b4fa-4552-b7b1-90412b155b2e
-- title:
--   BDL26 Finite Tanner Square: cellular Coboundary squared
-- statement:
--   The constructed cellular coboundaries compose to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L467-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L467-L472

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

theorem QEC.Coding.BDL26FiniteTannerSquare.cellularCoboundary_squared (P : TannerSquarePresentation) :
    (cellularCoboundary1 P).comp (cellularCoboundary0 P) = 0 := by sorry
