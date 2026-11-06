-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_minimum_height
-- name    : QEC.Locality.DaiLiHorizontalAtomization.minimum_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:38.443949+00:00
-- url     : https://prove2.me/theorems/6b76bd20-df35-464b-8cea-e31c8e6ce7a5
-- title:
--   Dai Li Horizontal Atomization: minimum height
-- statement:
--   Every nonempty atomization inherits the minimum physical height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1200-L1209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1200-L1209

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

theorem QEC.Locality.DaiLiHorizontalAtomization.minimum_height
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) :
    5 * ell ≤ upper - lower := by sorry
