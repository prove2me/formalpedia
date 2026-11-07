-- Prove2me | Theorems.Thm_QEC_Locality_daiLiHorizontalAtomization_last_upper
-- name    : QEC.Locality.daiLiHorizontalAtomization_last_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:57.396904+00:00
-- url     : https://prove2.me/theorems/37aa1c8e-e031-47df-9e69-688a5d403f45
-- title:
--   Locality: dai Li Horizontal Atomization last upper
-- statement:
--   An atomization reaches its declared upper endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L712-L723
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L712-L723

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

theorem QEC.Locality.daiLiHorizontalAtomization_last_upper
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hNonempty : atoms ≠ []) :
    (atoms.getLast hNonempty).2 = upper := by sorry
