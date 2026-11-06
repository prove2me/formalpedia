-- Prove2me | Theorems.Thm_QEC_Locality_exists_real_in_openInterval_not_mem_finset
-- name    : QEC.Locality.exists_real_in_openInterval_not_mem_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:54.195828+00:00
-- url     : https://prove2.me/theorems/d613d251-38ba-4e09-99b2-6a017fc54d72
-- title:
--   Locality: exists real in open Interval not mem finset
-- statement:
--   A finite set cannot occupy every point of a nonempty real interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L38-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L38-L46

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

theorem QEC.Locality.exists_real_in_openInterval_not_mem_finset
    (support : Finset ℝ) {lower upper : ℝ} (hInterval : lower < upper) :
    ∃ cut : ℝ, lower < cut ∧ cut < upper ∧ cut ∉ support := by sorry
