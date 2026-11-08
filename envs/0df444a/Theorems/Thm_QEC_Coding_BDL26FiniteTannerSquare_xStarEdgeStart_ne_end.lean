-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_xStarEdgeStart_ne_end
-- name    : QEC.Coding.BDL26FiniteTannerSquare.xStarEdgeStart_ne_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:20:09.385086+00:00
-- url     : https://prove2.me/theorems/9b01f806-b4ac-4534-958c-9f56207eab51
-- title:
--   BDL26 Finite Tanner Square: x Star Edge Start ne end
-- statement:
--   Every tagged original star edge has different typed endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1872-L1877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1872-L1877

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

theorem QEC.Coding.BDL26FiniteTannerSquare.xStarEdgeStart_ne_end (P : TannerSquarePresentation) (x : P.X)
    (edge : XStarEdge P x) :
    xStarEdgeStart P x edge ≠ xStarEdgeEnd P x edge := by sorry
