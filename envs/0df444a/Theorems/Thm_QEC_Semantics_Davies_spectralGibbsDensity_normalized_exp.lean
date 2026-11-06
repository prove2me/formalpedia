-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_spectralGibbsDensity_normalized_exp
-- name    : QEC.Semantics.Davies.spectralGibbsDensity_normalized_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:05:27.928407+00:00
-- url     : https://prove2.me/theorems/bff0c2ea-a157-4eca-81c2-760bfaa21bbe
-- title:
--   Davies: spectral Gibbs Density normalized exp
-- statement:
--   The spectral density is a normalized actual operator exponential for any
--   actual Hamiltonian eigenbasis, not merely for the chosen canonical basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L114-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L114-L135

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

theorem QEC.Semantics.Davies.spectralGibbsDensity_normalized_exp (H : Operator V)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator =
      ((gibbsPartitionFunction β e : ℂ)⁻¹) •
        (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H)).toLinearMap := by sorry
