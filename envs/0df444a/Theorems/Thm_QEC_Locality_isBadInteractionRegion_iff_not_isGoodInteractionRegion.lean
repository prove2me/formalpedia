-- Prove2me | Theorems.Thm_QEC_Locality_isBadInteractionRegion_iff_not_isGoodInteractionRegion
-- name    : QEC.Locality.isBadInteractionRegion_iff_not_isGoodInteractionRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:44:35.3294+00:00
-- url     : https://prove2.me/theorems/41f4e023-44fa-4a26-8a3a-8ac56e70dbe5
-- title:
--   Locality: is Bad Interaction Region iff not is Good Interaction Region
-- statement:
--   The Locality construction uses the is Bad Interaction Region iff not is Good Interaction Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1959-L1965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1959-L1965

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

theorem QEC.Locality.isBadInteractionRegion_iff_not_isGoodInteractionRegion
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (region : Finset ι) :
    IsBadInteractionRegion P embedding threshold d region ↔
      ¬ IsGoodInteractionRegion P embedding threshold d region := by sorry
