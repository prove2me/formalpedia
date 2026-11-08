-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_TannerSquareCellularRegular_faceOver_subsingleton
-- name    : QEC.Coding.BDL26FiniteTannerSquare.TannerSquareCellularRegular.faceOver_subsingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:57.052817+00:00
-- url     : https://prove2.me/theorems/e7a4d8fe-5f69-492b-b530-147895ca0a26
-- title:
--   Tanner Square Cellular Regular: face Over subsingleton
-- statement:
--   Every fixed X/Z face fiber is subsingleton.  This is theorem-derived from
--   the raw injectivity field rather than stored as a second regularity field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L130-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L130-L139

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

theorem QEC.Coding.BDL26FiniteTannerSquare.TannerSquareCellularRegular.faceOver_subsingleton
    {P : TannerSquarePresentation} (R : TannerSquareCellularRegular P)
    (x : P.X) (z : P.Z) : Subsingleton (FaceOver P.data x z) := by sorry
