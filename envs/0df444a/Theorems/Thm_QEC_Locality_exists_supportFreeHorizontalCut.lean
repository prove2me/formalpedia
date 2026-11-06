-- Prove2me | Theorems.Thm_QEC_Locality_exists_supportFreeHorizontalCut
-- name    : QEC.Locality.exists_supportFreeHorizontalCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:00.276114+00:00
-- url     : https://prove2.me/theorems/4946ffd8-68b8-4fb8-a876-fe330e6ef3a6
-- title:
--   Locality: exists support Free Horizontal Cut
-- statement:
--   An actual support-free horizontal cut can be selected inside every nonempty
--   open window.  It avoids every qubit coordinate in the parent rectangle, so
--   half-open ownership has no ambiguous internal boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L53-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L53-L65

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

theorem QEC.Locality.exists_supportFreeHorizontalCut
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    {lower upper : ℝ} (hInterval : lower < upper) :
    ∃ cut : ℝ, lower < cut ∧ cut < upper ∧
      ∀ q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper,
        (embedding.point q).2 ≠ cut := by sorry
