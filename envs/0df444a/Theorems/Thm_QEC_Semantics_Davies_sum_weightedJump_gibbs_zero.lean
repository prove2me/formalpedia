-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_sum_weightedJump_gibbs_zero
-- name    : QEC.Semantics.Davies.sum_weightedJump_gibbs_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:21.274279+00:00
-- url     : https://prove2.me/theorems/5c02cee3-4030-4504-8061-a0dbb85d8e48
-- title:
--   Davies: sum weighted Jump gibbs zero
-- statement:
--   Detailed balance cancels the gain at frequency `-ω` against loss at `ω`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L178-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L178-L204

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

theorem QEC.Semantics.Davies.sum_weightedJump_gibbs_zero {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (hA : ∀ a, (A a).IsSymmetric)
    (hDB : ∀ a w, rate a (negFrequency e w) = Real.exp (-β*w.val) * rate a w)
    (a : κ) :
    (∑ w : Frequency e, lindbladJumpTerm (weightedJump b e A rate (a,w))
      (spectralGibbsDensity b e β).toOperator) = 0 := by sorry
