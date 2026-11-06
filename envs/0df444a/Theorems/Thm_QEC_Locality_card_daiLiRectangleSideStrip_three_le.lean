-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiRectangleSideStrip_three_le
-- name    : QEC.Locality.card_daiLiRectangleSideStrip_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:43:33.073859+00:00
-- url     : https://prove2.me/theorems/91285f5c-af39-43b2-a624-fe69c4bbb912
-- title:
--   Locality: card dai Li Rectangle Side Strip three le
-- statement:
--   The Locality construction uses the card dai Li Rectangle Side Strip three le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1782-L1797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1782-L1797

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

theorem QEC.Locality.card_daiLiRectangleSideStrip_three_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.1 - lower.1 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 3).card : ℝ) ≤
      12 * ell * (upper.1 - lower.1 - 4 * ell) := by sorry
