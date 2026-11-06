-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_spectralGibbsDensity_diagonal
-- name    : QEC.Semantics.Davies.spectralGibbsDensity_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:05:00.25799+00:00
-- url     : https://prove2.me/theorems/ddee21aa-64a2-48dd-8e00-c63b006fe746
-- title:
--   Davies: spectral Gibbs Density diagonal
-- statement:
--   The existing Gibbs density is the diagonal spectral operator, with one
--   Boltzmann weight for each basis vector, including spectral multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L17-L19
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L17-L19

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

theorem QEC.Semantics.Davies.spectralGibbsDensity_diagonal (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator = diagonal b (gibbsProbability β e) := by sorry
