-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atom_bounds
-- name    : QEC.Locality.DaiLiHorizontalAtomization.atom_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:58.075202+00:00
-- url     : https://prove2.me/theorems/0cad4a51-1efe-427b-b814-bd17e59865b2
-- title:
--   Dai Li Horizontal Atomization: atom bounds
-- statement:
--   Every atom of a finite Dai--Li atomization remains inside its declared
--   parent interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L404-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L404-L423

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.DaiLiHorizontalAtomization.atom_bounds
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    lower ≤ atom.1 ∧ atom.2 ≤ upper := by sorry
