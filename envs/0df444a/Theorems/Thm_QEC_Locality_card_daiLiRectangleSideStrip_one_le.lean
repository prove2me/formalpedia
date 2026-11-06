-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiRectangleSideStrip_one_le
-- name    : QEC.Locality.card_daiLiRectangleSideStrip_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:41:36.26684+00:00
-- url     : https://prove2.me/theorems/29a330d4-40f0-4436-a87d-e3c3ccce9cdd
-- title:
--   Locality: card dai Li Rectangle Side Strip one le
-- statement:
--   The Locality construction uses the card dai Li Rectangle Side Strip one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1748-L1763
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1748-L1763

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

theorem QEC.Locality.card_daiLiRectangleSideStrip_one_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.2 - lower.2 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 1).card : ℝ) ≤
      12 * ell * (upper.2 - lower.2 - 4 * ell) := by sorry
