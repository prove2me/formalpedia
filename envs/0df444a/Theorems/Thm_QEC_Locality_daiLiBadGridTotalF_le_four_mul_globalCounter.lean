-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridTotalF_le_four_mul_globalCounter
-- name    : QEC.Locality.daiLiBadGridTotalF_le_four_mul_globalCounter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:22.726889+00:00
-- url     : https://prove2.me/theorems/aa60e493-7033-4196-8dd0-6a31f8e1bd87
-- title:
--   Locality: dai Li Bad Grid Total F le four mul global Counter
-- statement:
--   The bad-cell total inherits the same concrete global long-incidence bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L320-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L320-L328

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

theorem QEC.Locality.daiLiBadGridTotalF_le_four_mul_globalCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    {w : ℝ} (hw : 0 < w) (origin : ℝ × ℝ) :
    daiLiBadGridTotalF P embedding threshold d w origin ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by sorry
