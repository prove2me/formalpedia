-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivision_original_boundary_label
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivision_original_boundary_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:24:35.669642+00:00
-- url     : https://prove2.me/theorems/e9cca251-e476-4c96-a063-240da753f405
-- title:
--   BDL26 Finite Tanner Square: subdivision original boundary label
-- statement:
--   The original-vertex tag preserves the boundary label definitionally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L962-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L962-L965

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivision_original_boundary_label (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (v : XStarVertex P x) :
    subdivisionBoundaryVertexMember P x S (Sum.inl v) =
      xStarBoundaryVertexMember P x v.1 := by sorry
