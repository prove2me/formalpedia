-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_fixed_iff
-- name    : QEC.Semantics.Davies.energyProjector_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:11.816848+00:00
-- url     : https://prove2.me/theorems/3c4e3091-59dc-4ce5-935e-c1a0bb60919d
-- title:
--   Davies: energy Projector fixed iff
-- statement:
--   The Davies construction uses the energy Projector fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L420-L430
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L420-L430

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

theorem QEC.Semantics.Davies.energyProjector_fixed_iff (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (x : V) (E : ℝ) :
    energyProjector b e E x = x ↔ diagonal b e x = (E : ℂ) • x := by sorry
