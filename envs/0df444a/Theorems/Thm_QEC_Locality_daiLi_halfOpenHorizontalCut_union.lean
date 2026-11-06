-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_halfOpenHorizontalCut_union
-- name    : QEC.Locality.daiLi_halfOpenHorizontalCut_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:20.96939+00:00
-- url     : https://prove2.me/theorems/7b5f6248-bd52-4f06-8450-deb4dcb18e14
-- title:
--   Locality: dai Li half Open Horizontal Cut union
-- statement:
--   The half-open slices cover exactly the parent rectangle's finite qubit assignment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L92-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L92-L102

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

theorem QEC.Locality.daiLi_halfOpenHorizontalCut_union
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) :
    daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut ∪
        daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut =
      embedding.qubitsInRectangle rectangleLower rectangleUpper := by sorry
