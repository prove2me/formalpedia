-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiHorizontalAtomization_of_budget
-- name    : QEC.Locality.exists_daiLiHorizontalAtomization_of_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:47.289607+00:00
-- url     : https://prove2.me/theorems/3f2b7559-f486-4b90-a2f8-1593652a2941
-- title:
--   Locality: exists dai Li Horizontal Atomization of budget
-- statement:
--   The finite atomization is well-founded on an explicit Nat height budget.  A
--   non-base step removes a support-free band of height strictly between
--   `5 * ell` and `10 * ell`, so the remaining budget decreases by one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L235-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L235-L260

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

theorem QEC.Locality.exists_daiLiHorizontalAtomization_of_budget
    (support : Finset ℝ) (ell : ℝ) (hEll : 0 < ell) (budget : Nat)
    (lower upper : ℝ) (hMin : 5 * ell ≤ upper - lower)
    (hMax : upper - lower ≤ 20 * ell + (budget : ℝ) * (5 * ell)) :
    ∃ atoms, DaiLiHorizontalAtomization support ell lower upper atoms := by sorry
