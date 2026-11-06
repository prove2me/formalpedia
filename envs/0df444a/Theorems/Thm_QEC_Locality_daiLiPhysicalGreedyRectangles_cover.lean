-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_cover
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:06.86849+00:00
-- url     : https://prove2.me/theorems/dd788b9c-f379-4504-91c6-452f878471e0
-- title:
--   Locality: dai Li Physical Greedy Rectangles cover
-- statement:
--   The collapsed physical greedy rectangles cover exactly the actual qubits of
--   their parent rectangle.  This is a finite half-open assignment cover: all
--   internal cuts are globally support-free.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1406-L1436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1406-L1436

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_cover
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    daiLiRectangleQubitsCover embedding
        (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms) =
      embedding.qubitsInRectangle (left, lower) (right, upper) := by sorry
