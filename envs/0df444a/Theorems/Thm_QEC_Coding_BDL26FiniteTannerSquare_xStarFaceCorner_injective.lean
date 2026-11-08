-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_xStarFaceCorner_injective
-- name    : QEC.Coding.BDL26FiniteTannerSquare.xStarFaceCorner_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:24:11.346801+00:00
-- url     : https://prove2.me/theorems/487df64a-bf02-46e4-b380-5e089bee26b2
-- title:
--   BDL26 Finite Tanner Square: x Star Face Corner injective
-- statement:
--   The four tagged vertices of one original face are pairwise distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1119-L1129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1119-L1129

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

theorem QEC.Coding.BDL26FiniteTannerSquare.xStarFaceCorner_injective
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    Function.Injective (xStarFaceCorner P x f) := by sorry
