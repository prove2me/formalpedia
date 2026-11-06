-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_gibbs
-- name    : QEC.Semantics.Davies.frequencyComponent_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:04:54.623144+00:00
-- url     : https://prove2.me/theorems/0d2b0371-2270-4ec4-bc33-a3c85ce7446a
-- title:
--   Davies: frequency Component gibbs
-- statement:
--   The frequency sign matches energy transferred from the system to the bath.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L29-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L29-L44

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

theorem QEC.Semantics.Davies.frequencyComponent_gibbs (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β ω : ℝ) (A : Operator V) :
    frequencyComponent b e A ω * (spectralGibbsDensity b e β).toOperator =
      (Real.exp (-β * ω) : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * frequencyComponent b e A ω) := by sorry
