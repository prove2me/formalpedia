-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadInteractionSquareFamily_empty_or_total_lower
-- name    : QEC.Locality.daiLiBadInteractionSquareFamily_empty_or_total_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:55:52.875618+00:00
-- url     : https://prove2.me/theorems/77c9e6d6-0f69-4713-8a97-93afc338643c
-- title:
--   Locality: dai Li Bad Interaction Square Family empty or total lower
-- statement:
--   The exact nonempty-bad alternative needed by the #386 integer-count handoff.
--   For an empty family the total output count is zero; otherwise any selected bad
--   square contributes enough actual counter mass to give `d <= 10 * totalF`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1938-L1962
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1938-L1962

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

theorem QEC.Locality.daiLiBadInteractionSquareFamily_empty_or_total_lower
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (squares : Finset α) (center : α → ℝ × ℝ) (radius : α → ℝ)
    (rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hBad : ∀ square ∈ squares,
      IsBadInteractionSquare P embedding threshold d (center square) (radius square)) :
    (∑ square ∈ squares, (rectangles square).length) = 0 ∨
      d ≤ 10 * ∑ square ∈ squares,
        regionInteractionCounter P embedding threshold
          (squareQubits embedding (center square) (radius square)) := by sorry
