-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_vonNeumannEntropy_le_sum_log_selectedDimensions
-- name    : QEC.Semantics.QuditSubsystem.vonNeumannEntropy_le_sum_log_selectedDimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:19:37.647621+00:00
-- url     : https://prove2.me/theorems/023ac665-6e07-4198-9a23-1318d6522b8f
-- title:
--   Qudit Subsystem: von Neumann Entropy le sum log selected Dimensions
-- statement:
--   Maximum entropy on a concrete selected qudit system is bounded by its heterogeneous log sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L193-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L193-L201

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

theorem QEC.Semantics.QuditSubsystem.vonNeumannEntropy_le_sum_log_selectedDimensions (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    rho.vonNeumannEntropy <= ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by sorry
