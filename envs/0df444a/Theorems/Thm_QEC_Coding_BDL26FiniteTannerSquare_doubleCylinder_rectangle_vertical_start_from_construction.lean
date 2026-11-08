-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinder_rectangle_vertical_start_from_construction
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinder_rectangle_vertical_start_from_construction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:30:35.77354+00:00
-- url     : https://prove2.me/theorems/4f085125-19a8-48d7-882a-c32083c704d2
-- title:
--   BDL26 Finite Tanner Square: double Cylinder rectangle vertical start from construction
-- statement:
--   Assumption-free start-vertical incidence, derived from constructed boundary
--   nondegeneracy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2457-L2464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2457-L2464

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

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinder_rectangle_vertical_start_from_construction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle))
      (Sum.inr rectangle) = 1 := by sorry
