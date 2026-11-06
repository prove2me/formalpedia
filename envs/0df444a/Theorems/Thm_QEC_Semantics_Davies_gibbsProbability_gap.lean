-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_gibbsProbability_gap
-- name    : QEC.Semantics.Davies.gibbsProbability_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:30.909529+00:00
-- url     : https://prove2.me/theorems/0dac2829-b6f0-490c-bc02-483472aa4817
-- title:
--   Davies: gibbs Probability gap
-- statement:
--   The Davies construction uses the gibbs Probability gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L21-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L21-L26

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

theorem QEC.Semantics.Davies.gibbsProbability_gap (e : ι → ℝ) (β : ℝ) (i j : ι) :
    gibbsProbability β e j = Real.exp (-β * (e j-e i)) * gibbsProbability β e i := by sorry
