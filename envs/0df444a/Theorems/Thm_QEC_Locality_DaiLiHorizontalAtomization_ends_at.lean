-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_ends_at
-- name    : QEC.Locality.DaiLiHorizontalAtomization.ends_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:15:43.286325+00:00
-- url     : https://prove2.me/theorems/3e64599f-0d15-4d8c-9f6b-22eaf5e300da
-- title:
--   Dai Li Horizontal Atomization: ends at
-- statement:
--   An atomization reaches its declared upper endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1140-L1151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1140-L1151

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

theorem QEC.Locality.DaiLiHorizontalAtomization.ends_at
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hNonempty : atoms ≠ []) :
    (atoms.getLast hNonempty).2 = upper := by sorry
