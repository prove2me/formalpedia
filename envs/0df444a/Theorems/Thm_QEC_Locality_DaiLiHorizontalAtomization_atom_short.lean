-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atom_short
-- name    : QEC.Locality.DaiLiHorizontalAtomization.atom_short
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:36.279194+00:00
-- url     : https://prove2.me/theorems/ca46549f-5770-4268-a4cc-3013eb2ac3ea
-- title:
--   Dai Li Horizontal Atomization: atom short
-- statement:
--   Every atom emitted by an atomization has the required short-height bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L322-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L322-L336

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

theorem QEC.Locality.DaiLiHorizontalAtomization.atom_short
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    DaiLiShortHeight ell atom.1 atom.2 := by sorry
