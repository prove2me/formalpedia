-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_halfOpenCuts_eq_previous_api_of_supportFree
-- name    : QEC.Locality.daiLi_halfOpenCuts_eq_previous_api_of_supportFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:04.672345+00:00
-- url     : https://prove2.me/theorems/8152b05c-4de2-48e5-816d-8445157e9e6c
-- title:
--   Locality: dai Li half Open Cuts eq previous api of support Free
-- statement:
--   At a support-free cut, the new half-open ownership agrees extensionally with
--   the PR #493 lower/upper API; the difference is only boundary convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L124-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L124-L161

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLi_halfOpenCuts_eq_previous_api_of_supportFree
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ)
    (hSupportFree : ∀ q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper,
      (embedding.point q).2 ≠ cut) :
    daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut =
        lowerHorizontalRectangleQubits embedding rectangleLower rectangleUpper cut ∧
      daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut =
        upperHorizontalRectangleQubits embedding rectangleLower rectangleUpper cut := by sorry
