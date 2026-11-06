-- Prove2me | Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
-- name    : QEC.Locality.squareGrowthRadius_succ_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:57.727739+00:00
-- url     : https://prove2.me/theorems/c93a21d7-46da-44ce-b40c-c7ab65529b1e
-- title:
--   Locality: square Growth Radius succ sub
-- statement:
--   The Locality construction uses the square Growth Radius succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L496-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L496-L500

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

theorem QEC.Locality.squareGrowthRadius_succ_sub (baseRadius threshold : ℝ) (step : Nat) :
    squareGrowthRadius baseRadius threshold (step + 1) - threshold =
      squareGrowthRadius baseRadius threshold step := by sorry
