-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_gibbs_square_commute
-- name    : QEC.Semantics.Davies.frequencyComponent_gibbs_square_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:34.897884+00:00
-- url     : https://prove2.me/theorems/fea7dfc1-5880-40e6-866e-3c0672e18a90
-- title:
--   Davies: frequency Component gibbs square commute
-- statement:
--   The Davies construction uses the frequency Component gibbs square commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L137-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L137-L158

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

theorem QEC.Semantics.Davies.frequencyComponent_gibbs_square_commute (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β ω : ℝ) (A : Operator V) :
    Commute (LinearMap.adjoint (frequencyComponent b e A ω) * frequencyComponent b e A ω)
      (spectralGibbsDensity b e β).toOperator := by sorry
