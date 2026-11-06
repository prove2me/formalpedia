-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_add
-- name    : QEC.Semantics.Davies.frequencyComponent_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:24.350361+00:00
-- url     : https://prove2.me/theorems/6d679173-7a3c-4c76-a9c5-20ed9ddcef9d
-- title:
--   Davies: frequency Component add
-- statement:
--   The Davies construction uses the frequency Component add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L223-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L223-L230

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.frequencyComponent_add (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A B : Operator V) (ω : ℝ) :
    frequencyComponent b energy (A+B) ω = frequencyComponent b energy A ω +
      frequencyComponent b energy B ω := by sorry
