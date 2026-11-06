-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_log_finrank_selectedSystem_eq_sum_log_selectedDimensions
-- name    : QEC.Semantics.QuditSubsystem.log_finrank_selectedSystem_eq_sum_log_selectedDimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:40.638829+00:00
-- url     : https://prove2.me/theorems/2768f158-1c44-4110-bc08-0012daecbe28
-- title:
--   Qudit Subsystem: log finrank selected System eq sum log selected Dimensions
-- statement:
--   The base-two logarithm of a concrete selected-register dimension is its local log sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L182-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L182-L190

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

theorem QEC.Semantics.QuditSubsystem.log_finrank_selectedSystem_eq_sum_log_selectedDimensions (S : QuditSubsystem q)
    (hq : forall i, i ∈ S.selected -> 0 < q i) :
    Real.logb 2 (Module.finrank Complex S.selectedSystem : Real) =
      ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by sorry
