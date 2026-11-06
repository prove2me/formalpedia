-- Prove2me | Theorems.Thm_QEC_Locality_card_longOutsideNeighborsOf_le_sum_counter
-- name    : QEC.Locality.card_longOutsideNeighborsOf_le_sum_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:28.128903+00:00
-- url     : https://prove2.me/theorems/4695903c-5260-4280-bf5f-aac9308d4792
-- title:
--   Locality: card long Outside Neighbors Of le sum counter
-- statement:
--   The Locality construction uses the card long Outside Neighbors Of le sum counter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L128-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L128-L135

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

theorem QEC.Locality.card_longOutsideNeighborsOf_le_sum_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) :
    (longOutsideNeighborsOf P embedding threshold region).card ≤
      ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q := by sorry
