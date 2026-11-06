-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_log_selectedDimensions_le_card_mul_log_uniformDimension
-- name    : QEC.Semantics.QuditSubsystem.sum_log_selectedDimensions_le_card_mul_log_uniformDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:08:17.963192+00:00
-- url     : https://prove2.me/theorems/6825d063-18a2-46c8-ac50-6d794022b845
-- title:
--   Qudit Subsystem: sum log selected Dimensions le card mul log uniform Dimension
-- statement:
--   A uniform local-dimension bound controls the selected-region heterogeneous log sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L204-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L204-L217

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}

theorem QEC.Semantics.QuditSubsystem.sum_log_selectedDimensions_le_card_mul_log_uniformDimension (S : QuditSubsystem q)
    (hq : forall i, 0 < q i) (D : Nat)
    (hD : forall i, i ∈ S.selected -> q i <= D) :
    (∑ i ∈ S.selected, Real.logb 2 (q i : Real)) <=
      (S.selected.card : Real) * Real.logb 2 (D : Real) := by sorry
