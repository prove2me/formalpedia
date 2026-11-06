-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiBadInteractionSquareFamilySubdivision
-- name    : QEC.Locality.exists_daiLiBadInteractionSquareFamilySubdivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:19.449715+00:00
-- url     : https://prove2.me/theorems/6785e044-ab37-4371-8986-38388b17f5b3
-- title:
--   Locality: exists dai Li Bad Interaction Square Family Subdivision
-- statement:
--   A finite family of actual bad squares admits constructed physical subdivisions
--   whose total rectangle count satisfies the project-owned corrected factor-30
--   bound.  The internal choice is only over the explicitly proved terminating
--   atomization construction; each selected atom list is returned with its proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1747-L1871
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1747-L1871

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

theorem QEC.Locality.exists_daiLiBadInteractionSquareFamilySubdivision
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (squares : Finset α) (center : α → ℝ × ℝ) (radius : α → ℝ)
    (hEll : 0 < ell)
    (hHeight : ∀ square ∈ squares, 5 * ell ≤ 2 * radius square)
    (hBad : ∀ square ∈ squares,
      IsBadInteractionSquare P embedding threshold d (center square) (radius square)) :
    ∃ (atoms : α → List (ℝ × ℝ))
      (rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ square ∈ squares,
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((center square).2 - radius square) ((center square).2 + radius square)
          (atoms square)) ∧
      (∀ square ∈ squares,
        rectangles square = daiLiPhysicalGreedyRectangles P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square)
          d (atoms square)) ∧
      (∀ square ∈ squares,
        (rectangles square).IsChain (fun first second => first.2.2 = second.1.2)) ∧
      (∀ square ∈ squares,
        DaiLiPairwiseDisjointQubitRectangles embedding (rectangles square)) ∧
      (∀ square ∈ squares,
        daiLiRectangleQubitsCover embedding (rectangles square) =
          squareQubits embedding (center square) (radius square)) ∧
      (∀ square ∈ squares, ∀ rectangle ∈ rectangles square,
        5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
          (10 * regionInteractionCounter P embedding threshold
              (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
            rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      (∑ square ∈ squares, (rectangles square).length) * d ≤
        30 * ∑ square ∈ squares,
          regionInteractionCounter P embedding threshold
            (squareQubits embedding (center square) (radius square)) := by sorry
