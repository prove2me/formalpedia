-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_mul_left
-- name    : QEC.Semantics.Davies.frequencyComponent_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:02:51.357266+00:00
-- url     : https://prove2.me/theorems/e76c2454-ca49-45d0-acdb-aab9c52d0274
-- title:
--   Davies: frequency Component mul left
-- statement:
--   The Davies construction uses the frequency Component mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L288-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L288-L304

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

theorem QEC.Semantics.Davies.frequencyComponent_mul_left (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A B : Operator V) (hA : Commute (diagonal b e) A) (ω : ℝ) :
    frequencyComponent b e (A * B) ω = A * frequencyComponent b e B ω := by sorry
