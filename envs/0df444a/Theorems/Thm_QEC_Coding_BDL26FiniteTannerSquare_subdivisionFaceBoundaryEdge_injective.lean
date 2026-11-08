-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceBoundaryEdge_injective
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionFaceBoundaryEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:55.82054+00:00
-- url     : https://prove2.me/theorems/f310e61d-aab7-4053-8393-93925c86a682
-- title:
--   BDL26 Finite Tanner Square: subdivision Face Boundary Edge injective
-- statement:
--   The four boundary edges of a small square retain distinct local slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1848-L1869
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1848-L1869

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionFaceBoundaryEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    Function.Injective (subdivisionFaceBoundaryEdge P x S face) := by sorry
