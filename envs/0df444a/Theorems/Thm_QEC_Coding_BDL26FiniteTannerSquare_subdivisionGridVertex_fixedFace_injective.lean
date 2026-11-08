-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionGridVertex_fixedFace_injective
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_fixedFace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:36.362038+00:00
-- url     : https://prove2.me/theorems/7a395851-8f5b-492c-ade5-bf2aad439bf9
-- title:
--   BDL26 Finite Tanner Square: subdivision Grid Vertex fixed Face injective
-- statement:
--   Grid coordinates are retained injectively inside every fixed original
--   face, including all four boundary sides and corners.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1468-L1475
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1468-L1475

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_fixedFace_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) :
    Function.Injective (fun ij : Fin (S.half + 1) × Fin (S.half + 1) =>
      subdivisionGridVertex P x S f ij.1 ij.2) := by sorry
