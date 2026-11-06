-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_lower_lt_upper
-- name    : QEC.Locality.DaiLiHorizontalAtomization.lower_lt_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:25.897568+00:00
-- url     : https://prove2.me/theorems/8efbc8b4-306a-4a5c-bab3-fd2e3fc9ad87
-- title:
--   Dai Li Horizontal Atomization: lower lt upper
-- statement:
--   Every atomization has a strictly positive total height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L305-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L305-L315

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

theorem QEC.Locality.DaiLiHorizontalAtomization.lower_lt_upper
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) : lower < upper := by sorry
