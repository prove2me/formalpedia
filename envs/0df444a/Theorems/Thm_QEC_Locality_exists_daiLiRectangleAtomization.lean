-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiRectangleAtomization
-- name    : QEC.Locality.exists_daiLiRectangleAtomization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:26.685729+00:00
-- url     : https://prove2.me/theorems/3c830dc6-869d-4e66-b50b-8c01acd813a8
-- title:
--   Locality: exists dai Li Rectangle Atomization
-- statement:
--   The support-free atomization applies directly to the vertical span of an actual rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L280-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L280-L290

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

theorem QEC.Locality.exists_daiLiRectangleAtomization
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (ell : ℝ) (hEll : 0 < ell)
    (hHeight : 5 * ell ≤ rectangleUpper.2 - rectangleLower.2) :
    ∃ atoms,
      DaiLiHorizontalAtomization
        (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper)
        ell rectangleLower.2 rectangleUpper.2 atoms := by sorry
