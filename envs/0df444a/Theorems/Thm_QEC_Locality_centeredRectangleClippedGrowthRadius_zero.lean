-- Prove2me | Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
-- name    : QEC.Locality.centeredRectangleClippedGrowthRadius_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:20.128909+00:00
-- url     : https://prove2.me/theorems/78fd6812-875e-4c59-aa85-0d7029f2819f
-- title:
--   Locality: centered Rectangle Clipped Growth Radius zero
-- statement:
--   The Locality construction uses the centered Rectangle Clipped Growth Radius zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1505-L1508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1505-L1508

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

theorem QEC.Locality.centeredRectangleClippedGrowthRadius_zero
    (baseRadius targetRadius threshold : ℝ) (hBase : baseRadius ≤ targetRadius) :
    centeredRectangleClippedGrowthRadius baseRadius targetRadius threshold 0 = baseRadius := by sorry
