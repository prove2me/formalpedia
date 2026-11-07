-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_infix_span_le
-- name    : QEC.Locality.DaiLiHorizontalAtomization.infix_span_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:29.091067+00:00
-- url     : https://prove2.me/theorems/b7d5dd13-5fb0-4f3c-a6c9-148b3b92e96d
-- title:
--   Dai Li Horizontal Atomization: infix span le
-- statement:
--   The span of any nonempty contiguous greedy atom group is bounded by the
--   span of its original atomized parent interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L427-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L427-L444

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

theorem QEC.Locality.DaiLiHorizontalAtomization.infix_span_le
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms group : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) (hGroup : group <:+: atoms) (hGroupNe : group ≠ []) :
    daiLiAtomGroupUpper group - daiLiAtomGroupLower group ≤ upper - lower := by sorry
