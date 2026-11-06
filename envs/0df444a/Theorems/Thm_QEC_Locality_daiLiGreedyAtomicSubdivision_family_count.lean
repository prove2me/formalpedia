-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyAtomicSubdivision_family_count
-- name    : QEC.Locality.daiLiGreedyAtomicSubdivision_family_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:10.623233+00:00
-- url     : https://prove2.me/theorems/2ff964cd-5a3a-4fed-9175-e92683c2d15e
-- title:
--   Locality: dai Li Greedy Atomic Subdivision family count
-- statement:
--   The corrected finite-family count.  Each bad square supplies `d <= 10 * F_i`,
--   which absorbs the one additive `d` from every single-square construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L836-L868
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L836-L868

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

theorem QEC.Locality.daiLiGreedyAtomicSubdivision_family_count
    {α : Type*} [DecidableEq α] (d : Nat)
    (bands : α → List DaiLiAtomicCounter) (squares : Finset α)
    (hBad : ∀ square ∈ squares, d ≤ 10 * daiLiAtomicMass (bands square)) :
    (∑ square ∈ squares, (daiLiGreedyAtomicSubdivision d (bands square)).length) * d ≤
      30 * ∑ square ∈ squares, daiLiAtomicMass (bands square) := by sorry
