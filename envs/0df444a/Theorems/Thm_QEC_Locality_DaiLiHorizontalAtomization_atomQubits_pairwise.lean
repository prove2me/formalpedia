-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atomQubits_pairwise
-- name    : QEC.Locality.DaiLiHorizontalAtomization.atomQubits_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:07.076126+00:00
-- url     : https://prove2.me/theorems/b0554deb-256a-40bb-9800-65eee2ef21b2
-- title:
--   Dai Li Horizontal Atomization: atom Qubits pairwise
-- statement:
--   Distinct support-free atoms assign disjoint finite qubit sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L560-L598
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L560-L598

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

theorem QEC.Locality.DaiLiHorizontalAtomization.atomQubits_pairwise
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hEll : 0 < ell) :
    (atoms.map (daiLiAtomQubits embedding left right)).Pairwise Disjoint := by sorry
