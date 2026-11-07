-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiDGeKResidual_lt_of_separator_lt
-- name    : QEC.Locality.card_daiLiDGeKResidual_lt_of_separator_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:10.77419+00:00
-- url     : https://prove2.me/theorems/fb1b7f13-78d5-4974-b555-8e347b54f802
-- title:
--   Locality: card dai Li DGe KResidual lt of separator lt
-- statement:
--   A strict real-valued separator bound transfers to the actual residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L819-L829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L819-L829

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.card_daiLiDGeKResidual_lt_of_separator_lt
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell k : ℝ)
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell)
    (hSeparator : ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) < k) :
    ((daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected.card : ℝ) < k := by sorry
