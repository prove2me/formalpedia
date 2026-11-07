-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_first_lower
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_first_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:55.414362+00:00
-- url     : https://prove2.me/theorems/4bbaaa75-f68b-4ee5-8652-a76a97a2a1da
-- title:
--   Locality: dai Li Physical Greedy Rectangles first lower
-- statement:
--   The first rectangle of a nonempty greedy subdivision starts at the
--   declared lower atomization endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L671-L709
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L671-L709

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_first_lower
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell lower upper : ℝ) (d : Nat)
    (atoms : List (ℝ × ℝ))
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hLength : 0 < (daiLiPhysicalGreedyRectangles P embedding threshold left right
      d atoms).length) :
    ((daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).get
      ⟨0, hLength⟩).1.2 = lower := by sorry
