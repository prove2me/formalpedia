-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_halfOpenHorizontalCut_disjoint
-- name    : QEC.Locality.daiLi_halfOpenHorizontalCut_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:06.775763+00:00
-- url     : https://prove2.me/theorems/f6bedb6b-c197-4321-bdd7-e50a0f8bf185
-- title:
--   Locality: dai Li half Open Horizontal Cut disjoint
-- statement:
--   The two half-open slices are genuinely disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L82-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L82-L89

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

theorem QEC.Locality.daiLi_halfOpenHorizontalCut_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) :
    Disjoint (daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut)
      (daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut) := by sorry
