-- Prove2me | Theorems.Thm_QEC_Locality_card_longNeighborsOf_le_sum_counter
-- name    : QEC.Locality.card_longNeighborsOf_le_sum_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:02:49.73318+00:00
-- url     : https://prove2.me/theorems/a554ea76-1a95-4889-8d2c-1e5fc5f12c5c
-- title:
--   Locality: card long Neighbors Of le sum counter
-- statement:
--   A union bound converts local long incidences into an endpoint count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L112-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L112-L126

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

theorem QEC.Locality.card_longNeighborsOf_le_sum_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) :
    (longNeighborsOf P embedding threshold region).card ≤
      ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q := by sorry
