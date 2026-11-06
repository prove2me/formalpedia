-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_starts_at
-- name    : QEC.Locality.DaiLiHorizontalAtomization.starts_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:15.879327+00:00
-- url     : https://prove2.me/theorems/8ce4f26b-cd60-4093-bc00-c12c79a0347a
-- title:
--   Dai Li Horizontal Atomization: starts at
-- statement:
--   An atomization always starts at its declared lower endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L339-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L339-L345

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

theorem QEC.Locality.DaiLiHorizontalAtomization.starts_at
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    ∃ firstUpper tail, atoms = (lower, firstUpper) :: tail := by sorry
