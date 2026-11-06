-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_spectralGibbsDensity_basis_independent
-- name    : QEC.Semantics.Davies.spectralGibbsDensity_basis_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:02.952507+00:00
-- url     : https://prove2.me/theorems/7f3b2d0b-9d7f-428e-998c-c7c345ddc407
-- title:
--   Davies: spectral Gibbs Density basis independent
-- statement:
--   Any two genuine eigenbases produce the same existing Gibbs density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L240-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L240-L249

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

theorem QEC.Semantics.Davies.spectralGibbsDensity_basis_independent {ι' : Type} [Fintype ι'] [Nonempty ι']
    (H : Operator V) (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : OrthonormalBasis ι' ℂ V) (f : ι' → ℝ)
    (hb : ∀ i, H (b i) = (e i : ℂ) • b i)
    (hc : ∀ j, H (c j) = (f j : ℂ) • c j) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator = (spectralGibbsDensity c f β).toOperator := by sorry
