-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiRectangleSideStrip_zero_le
-- name    : QEC.Locality.card_daiLiRectangleSideStrip_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:41:36.42355+00:00
-- url     : https://prove2.me/theorems/e2cc2675-e0f8-484a-9a2c-c3369c5ab5e4
-- title:
--   Locality: card dai Li Rectangle Side Strip zero le
-- statement:
--   The left finite side strip obeys its exact area packing bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1731-L1746
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1731-L1746

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.card_daiLiRectangleSideStrip_zero_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.2 - lower.2 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 0).card : ℝ) ≤
      12 * ell * (upper.2 - lower.2 - 4 * ell) := by sorry
