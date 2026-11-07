-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_infix_bounds
-- name    : QEC.Locality.DaiLiHorizontalAtomization.infix_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:40.763273+00:00
-- url     : https://prove2.me/theorems/54737820-d5d1-41c5-8bbc-ab31d4a0d4e1
-- title:
--   Dai Li Horizontal Atomization: infix bounds
-- statement:
--   The lower and upper coordinates of a nonempty contiguous atom group stay
--   inside the original atomized interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L448-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L448-L465

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

theorem QEC.Locality.DaiLiHorizontalAtomization.infix_bounds
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms group : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) (hGroup : group <:+: atoms) (hGroupNe : group ≠ []) :
    lower ≤ daiLiAtomGroupLower group ∧ daiLiAtomGroupUpper group ≤ upper := by sorry
