-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiHorizontalAtomization_base
-- name    : QEC.Locality.exists_daiLiHorizontalAtomization_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:55.777191+00:00
-- url     : https://prove2.me/theorems/19af9b77-7140-436d-a6fc-13a4308273cc
-- title:
--   Locality: exists dai Li Horizontal Atomization base
-- statement:
--   Any interval between five and twenty `ell` has a finite support-free short atomization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L185-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L185-L228

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

theorem QEC.Locality.exists_daiLiHorizontalAtomization_base
    (support : Finset ℝ) (ell lower upper : ℝ) (hEll : 0 < ell)
    (hMin : 5 * ell ≤ upper - lower) (hMax : upper - lower ≤ 20 * ell) :
    ∃ atoms, DaiLiHorizontalAtomization support ell lower upper atoms := by sorry
