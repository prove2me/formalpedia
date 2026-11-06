-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_gibbs_stationary
-- name    : QEC.Semantics.Davies.weightedJump_gibbs_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:54.06439+00:00
-- url     : https://prove2.me/theorems/7f7c00e0-79ba-4e44-a06f-8294ee5744f3
-- title:
--   Davies: weighted Jump gibbs stationary
-- statement:
--   The Davies construction uses the weighted Jump gibbs stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L206-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L206-L213

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

theorem QEC.Semantics.Davies.weightedJump_gibbs_stationary {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (β : ℝ)
    (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (hA : ∀ a, (A a).IsSymmetric)
    (hDB : ∀ a w, rate a (negFrequency e w) = Real.exp (-β*w.val) * rate a w) :
    lindbladDissipator (weightedJump b e A rate) (spectralGibbsDensity b e β).toOperator = 0 := by sorry
