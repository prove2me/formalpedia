-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiBadInteractionSquareSubdivision
-- name    : QEC.Locality.exists_daiLiBadInteractionSquareSubdivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:55:40.591927+00:00
-- url     : https://prove2.me/theorems/f614b55c-bde2-408c-8e9e-a7e6db679782
-- title:
--   Locality: exists dai Li Bad Interaction Square Subdivision
-- statement:
--   Every actual bad square of sufficient height has a constructed corrected
--   subdivision.  The returned atomization carries the support-free cuts and its
--   termination proof; the returned rectangle list is its greedy physical image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1683-L1739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1683-L1739

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

theorem QEC.Locality.exists_daiLiBadInteractionSquareSubdivision
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (center : ℝ × ℝ) (radius : ℝ)
    (hEll : 0 < ell) (hHeight : 5 * ell ≤ 2 * radius)
    (hBad : IsBadInteractionSquare P embedding threshold d center radius) :
    ∃ atoms rectangles,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        (center.2 - radius) (center.2 + radius) atoms ∧
      rectangles = daiLiPhysicalGreedyRectangles P embedding threshold
        (center.1 - radius) (center.1 + radius) d atoms ∧
      rectangles.IsChain (fun first second => first.2.2 = second.1.2) ∧
      DaiLiPairwiseDisjointQubitRectangles embedding rectangles ∧
      daiLiRectangleQubitsCover embedding rectangles =
        squareQubits embedding center radius ∧
      (∀ rectangle ∈ rectangles,
        5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
          (10 * regionInteractionCounter P embedding threshold
              (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
            rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      rectangles.length * d ≤
        20 * regionInteractionCounter P embedding threshold
          (squareQubits embedding center radius) + d ∧
      d ≤ 10 * regionInteractionCounter P embedding threshold
        (squareQubits embedding center radius) := by sorry
