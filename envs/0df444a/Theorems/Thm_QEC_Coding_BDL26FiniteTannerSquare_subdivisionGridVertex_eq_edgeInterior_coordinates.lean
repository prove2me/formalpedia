-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionGridVertex_eq_edgeInterior_coordinates
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_eq_edgeInterior_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:29:21.730204+00:00
-- url     : https://prove2.me/theorems/568634d1-77f6-485e-ab9b-9cea59149906
-- title:
--   BDL26 Finite Tanner Square: subdivision Grid Vertex eq edge Interior coordinates
-- statement:
--   A grid vertex equal to a stored edge-interior tag identifies the exact
--   side of the old face and retains the interior coordinate on that side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1505-L1551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1505-L1551

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_eq_edgeInterior_coordinates
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b : Fin (S.half + 1))
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (h : subdivisionGridVertex P x S face a b =
      Sum.inr (Sum.inl (edge, index))) :
    (edge = xStarFaceXQEdge P x face 1 ∧
        a.1 = 0 ∧ b.1 = index.1 + 1) ∨
      (edge = xStarFaceQZEdge P x face 0 ∧
        a.1 = S.half ∧ b.1 = index.1 + 1) ∨
      (edge = xStarFaceXQEdge P x face 0 ∧
        a.1 = index.1 + 1 ∧ b.1 = 0) ∨
      (edge = xStarFaceQZEdge P x face 1 ∧
        a.1 = index.1 + 1 ∧ b.1 = S.half) := by sorry
