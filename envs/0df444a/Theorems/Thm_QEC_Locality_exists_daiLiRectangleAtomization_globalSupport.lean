-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiRectangleAtomization_globalSupport
-- name    : QEC.Locality.exists_daiLiRectangleAtomization_globalSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:02.291783+00:00
-- url     : https://prove2.me/theorems/4b2657c2-976d-4506-98fc-30acfd2a7d4a
-- title:
--   Locality: exists dai Li Rectangle Atomization global Support
-- statement:
--   The rectangle atomization may use the stronger all-qubit support-free convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L293-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L293-L302

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

theorem QEC.Locality.exists_daiLiRectangleAtomization_globalSupport
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (ell : ℝ) (hEll : 0 < ell)
    (hHeight : 5 * ell ≤ rectangleUpper.2 - rectangleLower.2) :
    ∃ atoms,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
        ell rectangleLower.2 rectangleUpper.2 atoms := by sorry
