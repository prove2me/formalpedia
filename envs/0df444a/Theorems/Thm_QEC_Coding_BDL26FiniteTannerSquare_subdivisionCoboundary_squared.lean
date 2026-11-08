-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionCoboundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:55.029777+00:00
-- url     : https://prove2.me/theorems/a4ef00f5-6da5-41ee-b9fd-e769ec95f9e3
-- title:
--   BDL26 Finite Tanner Square: subdivision Coboundary squared
-- statement:
--   The constructed subdivision coboundary squares to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2054-L2060
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2054-L2060

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionCoboundary_squared (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    (subdivisionCoboundary1 P x S).comp (subdivisionCoboundary0 P x S) = 0 := by sorry
