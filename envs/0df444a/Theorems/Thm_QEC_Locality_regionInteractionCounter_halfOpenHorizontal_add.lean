-- Prove2me | Theorems.Thm_QEC_Locality_regionInteractionCounter_halfOpenHorizontal_add
-- name    : QEC.Locality.regionInteractionCounter_halfOpenHorizontal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:18.950619+00:00
-- url     : https://prove2.me/theorems/2021b836-dfbf-436d-825b-b3c201f3feb8
-- title:
--   Locality: region Interaction Counter half Open Horizontal add
-- statement:
--   The actual Dai--Li incidence counter is additive across the half-open split.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L105-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L105-L118

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

theorem QEC.Locality.regionInteractionCounter_halfOpenHorizontal_add
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (rectangleLower rectangleUpper : ℝ × ℝ) (cut : ℝ) :
    regionInteractionCounter P embedding threshold
        (daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut) +
      regionInteractionCounter P embedding threshold
        (daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut) =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle rectangleLower rectangleUpper) := by sorry
