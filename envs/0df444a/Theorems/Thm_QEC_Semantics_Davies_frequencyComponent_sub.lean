-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_sub
-- name    : QEC.Semantics.Davies.frequencyComponent_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:03:54.088312+00:00
-- url     : https://prove2.me/theorems/60220629-7b7c-4d73-b217-b9cbfa0f27d2
-- title:
--   Davies: frequency Component sub
-- statement:
--   The Davies construction uses the frequency Component sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L312-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L312-L319

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

theorem QEC.Semantics.Davies.frequencyComponent_sub (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A B : Operator V) (ω : ℝ) :
    frequencyComponent b e (A - B) ω = frequencyComponent b e A ω -
      frequencyComponent b e B ω := by sorry
