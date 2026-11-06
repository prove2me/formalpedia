-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atom_chain
-- name    : QEC.Locality.DaiLiHorizontalAtomization.atom_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:01.779232+00:00
-- url     : https://prove2.me/theorems/f7f1b38a-aced-4f54-b9ca-4f3b2837f1c9
-- title:
--   Dai Li Horizontal Atomization: atom chain
-- statement:
--   The source order of an atomization is a chain of exact common endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L348-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L348-L358

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

theorem QEC.Locality.DaiLiHorizontalAtomization.atom_chain
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    atoms.IsChain DaiLiAtomAdjacent := by sorry
