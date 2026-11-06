-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_mul_right
-- name    : QEC.Semantics.Davies.frequencyComponent_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:02:36.033223+00:00
-- url     : https://prove2.me/theorems/87a68d3d-e862-4972-bf6a-35be2176ca0d
-- title:
--   Davies: frequency Component mul right
-- statement:
--   The Davies construction uses the frequency Component mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L270-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L270-L286

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

theorem QEC.Semantics.Davies.frequencyComponent_mul_right (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A B : Operator V) (hB : Commute (diagonal b e) B) (ω : ℝ) :
    frequencyComponent b e (A * B) ω = frequencyComponent b e A ω * B := by sorry
