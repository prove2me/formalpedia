-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_TannerSquarePresentation_faceQ_injective
-- name    : QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation.faceQ_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:47.374323+00:00
-- url     : https://prove2.me/theorems/9ffb01fb-7220-46f5-b807-2b6362ee751b
-- title:
--   Tanner Square Presentation: face Q injective
-- statement:
--   The two ordered Q corners of every presented face are distinct.  This is a
--   consequence of the sole validity field, not an additional presentation axiom.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L99-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L99-L112

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
open QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation

theorem QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation.faceQ_injective (P : TannerSquarePresentation) (f : P.Face) :
    Function.Injective (P.faceQ f) := by sorry
