-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGridSideGood_disjoint
-- name    : QEC.Locality.daiLiGridSideGood_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:24.078908+00:00
-- url     : https://prove2.me/theorems/046fe7a4-451b-4c18-85fa-f575a73880bf
-- title:
--   Locality: dai Li Grid Side Good disjoint
-- statement:
--   Distinct good finite side strips have no shared qubits: geometrically they
--   are at least `ell` apart, and the code's separation threshold is positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1836-L1851
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1836-L1851

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

theorem QEC.Locality.daiLiGridSideGood_disjoint
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (threshold : ℝ) (hEll : 0 < ell) (hWidth : 4 * ell ≤ w) (origin : ℝ × ℝ)
    (side other : DaiLiGridSideIndex) (hne : side ≠ other) :
    Disjoint
      (daiLiGridSideGoodQubits P embedding threshold w ell origin side)
      (daiLiGridSideGoodQubits P embedding threshold w ell origin other) := by sorry
