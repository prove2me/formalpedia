-- Prove2me | Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_eq_target
-- name    : QEC.Locality.centeredRectangleClippedGrowthRadius_eq_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:00.062277+00:00
-- url     : https://prove2.me/theorems/862647f7-dfc6-427d-9fe0-3c92d69c28d4
-- title:
--   Locality: centered Rectangle Clipped Growth Radius eq target
-- statement:
--   The Locality construction uses the centered Rectangle Clipped Growth Radius eq target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1510-L1515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1510-L1515

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

theorem QEC.Locality.centeredRectangleClippedGrowthRadius_eq_target
    (baseRadius targetRadius threshold : ℝ) (steps : ℕ)
    (hReach : targetRadius ≤ baseRadius + steps * threshold) :
    centeredRectangleClippedGrowthRadius baseRadius targetRadius threshold steps =
      targetRadius := by sorry
