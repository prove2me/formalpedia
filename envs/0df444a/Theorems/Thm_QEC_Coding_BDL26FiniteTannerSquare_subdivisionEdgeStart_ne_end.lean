-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionEdgeStart_ne_end
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionEdgeStart_ne_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:48.346616+00:00
-- url     : https://prove2.me/theorems/f5f3153a-f07a-40b2-a102-1ac8a5206809
-- title:
--   BDL26 Finite Tanner Square: subdivision Edge Start ne end
-- statement:
--   Every explicitly constructed subdivision edge has distinct endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1901-L1925
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1901-L1925

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionEdgeStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    subdivisionEdgeStart P x S edge ≠ subdivisionEdgeEnd P x S edge := by sorry
