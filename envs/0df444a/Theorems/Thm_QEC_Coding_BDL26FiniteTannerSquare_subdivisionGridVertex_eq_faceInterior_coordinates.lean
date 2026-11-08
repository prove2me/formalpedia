-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionGridVertex_eq_faceInterior_coordinates
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_eq_faceInterior_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:29:28.031035+00:00
-- url     : https://prove2.me/theorems/bb3a9a6b-7b70-4c46-8c1e-9cd3d6588185
-- title:
--   BDL26 Finite Tanner Square: subdivision Grid Vertex eq face Interior coordinates
-- statement:
--   A grid vertex equal to a stored face-interior tag retains the old face
--   and both interior coordinates.  This proposition-level decoder is the public
--   boundary-normalization companion to `subdivisionGridVertex_fixedFace_injective`;
--   it returns no selected cell, edge, or path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1481-L1501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1481-L1501

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_eq_faceInterior_coordinates
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (first second : XStarFace P x)
    (a b : Fin (S.half + 1)) (i j : Fin (S.half - 1))
    (h : subdivisionGridVertex P x S first a b =
      Sum.inr (Sum.inr (second, i, j))) :
    first = second ∧ a.1 = i.1 + 1 ∧ b.1 = j.1 + 1 := by sorry
