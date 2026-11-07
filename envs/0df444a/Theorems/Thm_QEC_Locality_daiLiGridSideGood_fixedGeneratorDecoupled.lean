-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGridSideGood_fixedGeneratorDecoupled
-- name    : QEC.Locality.daiLiGridSideGood_fixedGeneratorDecoupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:13:14.472193+00:00
-- url     : https://prove2.me/theorems/72b94450-c22e-43ce-8efd-c2ea11503d77
-- title:
--   Locality: dai Li Grid Side Good fixed Generator Decoupled
-- statement:
--   The concrete finite good strips are pairwise fixed-generator decoupled.
--   This is the exact bridge from the proved coordinate separation to the CPTP
--   union closure, with long endpoints removed from both components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1856-L1873
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1856-L1873

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

theorem QEC.Locality.daiLiGridSideGood_fixedGeneratorDecoupled
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (hEll : 0 < ell) (hWidth : 4 * ell ≤ w) (threshold : ℝ)
    (hThreshold : threshold ≤ ell)
    (origin : ℝ × ℝ) (side other : DaiLiGridSideIndex) (hne : side ≠ other) :
    P.fixedGeneratorDecoupled
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin side : Finset ι) : Set ι)
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin other : Finset ι) : Set ι) := by sorry
