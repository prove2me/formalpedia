-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridTotalF_le_daiLiGridClosedTotalF
-- name    : QEC.Locality.daiLiBadGridTotalF_le_daiLiGridClosedTotalF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:33.141836+00:00
-- url     : https://prove2.me/theorems/cb987623-98e3-475f-ba17-49bad3d131de
-- title:
--   Locality: dai Li Bad Grid Total F le dai Li Grid Closed Total F
-- statement:
--   The Locality construction uses the dai Li Bad Grid Total F le dai Li Grid Closed Total F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L262-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L262-L273

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

theorem QEC.Locality.daiLiBadGridTotalF_le_daiLiGridClosedTotalF
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) :
    daiLiBadGridTotalF P embedding threshold d w origin ≤
      daiLiGridClosedTotalF P embedding threshold w origin := by sorry
