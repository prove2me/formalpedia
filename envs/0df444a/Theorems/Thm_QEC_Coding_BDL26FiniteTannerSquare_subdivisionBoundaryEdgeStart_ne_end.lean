-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionBoundaryEdgeStart_ne_end
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionBoundaryEdgeStart_ne_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:35.100258+00:00
-- url     : https://prove2.me/theorems/f04fcaab-a078-4250-9d7d-3abca8b91456
-- title:
--   BDL26 Finite Tanner Square: subdivision Boundary Edge Start ne end
-- statement:
--   Boundary labels do not identify the two endpoints of a constructed
--   boundary segment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2163-L2172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2163-L2172

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionBoundaryEdgeStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionBoundaryEdge P x S) :
    subdivisionBoundaryEdgeStart P x S edge ≠
      subdivisionBoundaryEdgeEnd P x S edge := by sorry
