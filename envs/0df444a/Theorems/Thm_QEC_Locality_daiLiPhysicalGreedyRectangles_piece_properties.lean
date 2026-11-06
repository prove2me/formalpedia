-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_piece_properties
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_piece_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:45.127164+00:00
-- url     : https://prove2.me/theorems/31d047d0-61ab-4cd1-89d3-65749175d332
-- title:
--   Locality: dai Li Physical Greedy Rectangles piece properties
-- statement:
--   Every output rectangle has the exact minimum-height and low-counter/short alternatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1563-L1582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1563-L1582

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_piece_properties
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) (rectangle : (ℝ × ℝ) × (ℝ × ℝ))
    (hRectangle : rectangle ∈ daiLiPhysicalGreedyRectangles
      P embedding threshold left right d atoms) :
    5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
      (10 * regionInteractionCounter P embedding threshold
          (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
        rectangle.2.2 - rectangle.1.2 ≤ 10 * ell) := by sorry
