-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_xqIncidenceMatrix_mul_qzIncidenceMatrix
-- name    : QEC.Coding.BDL26FiniteTannerSquare.xqIncidenceMatrix_mul_qzIncidenceMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:23:38.036471+00:00
-- url     : https://prove2.me/theorems/7c8ddc46-e982-4b40-adff-dee39b671b6a
-- title:
--   BDL26 Finite Tanner Square: xq Incidence Matrix mul qz Incidence Matrix
-- statement:
--   The Tanner incidence product vanishes by the explicit perfect pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L390-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L390-L406

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

theorem QEC.Coding.BDL26FiniteTannerSquare.xqIncidenceMatrix_mul_qzIncidenceMatrix (P : TannerSquarePresentation) :
    xqIncidenceMatrix P * qzIncidenceMatrix P = 0 := by sorry
