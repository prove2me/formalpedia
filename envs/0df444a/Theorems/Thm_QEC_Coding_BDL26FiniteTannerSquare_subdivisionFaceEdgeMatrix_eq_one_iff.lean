-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceEdgeMatrix_eq_one_iff
-- name    : QEC.Coding.BDL26FiniteTannerSquare.subdivisionFaceEdgeMatrix_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:29:44.952742+00:00
-- url     : https://prove2.me/theorems/74370755-42ad-489f-9e91-66826d26ea40
-- title:
--   BDL26 Finite Tanner Square: subdivision Face Edge Matrix eq one iff
-- statement:
--   Matrix incidence of a canonical small square is exactly membership in its
--   four locally enumerated boundary slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1952-L2001
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1952-L2001

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

theorem QEC.Coding.BDL26FiniteTannerSquare.subdivisionFaceEdgeMatrix_eq_one_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) (face : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S edge face = 1 ↔
      ∃ slot : Two × Two,
        subdivisionFaceBoundaryEdge P x S face slot = edge := by sorry
