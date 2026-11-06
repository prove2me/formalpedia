-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_adjoint
-- name    : QEC.Semantics.Davies.frequencyComponent_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:01:44.356519+00:00
-- url     : https://prove2.me/theorems/fedd6778-551b-456e-8180-666394013a37
-- title:
--   Davies: frequency Component adjoint
-- statement:
--   The Davies construction uses the frequency Component adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L211-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L211-L221

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

theorem QEC.Semantics.Davies.frequencyComponent_adjoint (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) (ω : ℝ) :
    LinearMap.adjoint (frequencyComponent b energy A ω) =
      frequencyComponent b energy (LinearMap.adjoint A) (-ω) := by sorry
