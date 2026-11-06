-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_dissipator_apply
-- name    : QEC.Semantics.Davies.weightedJump_dissipator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:09:21.358739+00:00
-- url     : https://prove2.me/theorems/38e9d32f-65db-45ea-a351-78482014b977
-- title:
--   Davies: weighted Jump dissipator apply
-- statement:
--   The complete weighted dissipator formula retains one coherent operator per gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L252-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L252-L259

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.weightedJump_dissipator_apply {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (rate : κ → Frequency e → ℝ) (hn : ∀ a w, 0 ≤ rate a w) (F : Operator V) :
    lindbladDissipator (weightedJump b e A rate) F =
      ∑ a, ∑ w : Frequency e, (rate a w : ℂ) •
        lindbladJumpTerm (frequencyComponent b e (A a) w.val) F := by sorry
