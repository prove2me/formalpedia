-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_gibbs_term
-- name    : QEC.Semantics.Davies.weightedJump_gibbs_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:11.819124+00:00
-- url     : https://prove2.me/theorems/cb927c8d-9aed-449c-aac6-ee7c626af9f7
-- title:
--   Davies: weighted Jump gibbs term
-- statement:
--   The Davies construction uses the weighted Jump gibbs term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L160-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L160-L175

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

theorem QEC.Semantics.Davies.weightedJump_gibbs_term {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (a : κ) (w : Frequency e) :
    lindbladJumpTerm (weightedJump b e A rate (a,w)) (spectralGibbsDensity b e β).toOperator =
      (rate a w * Real.exp (-β*w.val) : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * frequencyComponent b e (A a) w.val *
          LinearMap.adjoint (frequencyComponent b e (A a) w.val)) -
      (rate a w : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * LinearMap.adjoint (frequencyComponent b e (A a) w.val) *
          frequencyComponent b e (A a) w.val) := by sorry
