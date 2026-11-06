-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_adjoint
-- name    : QEC.Semantics.Davies.energyProjector_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:11.400792+00:00
-- url     : https://prove2.me/theorems/5b1bbc6f-779f-4f39-a60c-9066e6400a2c
-- title:
--   Davies: energy Projector adjoint
-- statement:
--   The Davies construction uses the energy Projector adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L112-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L112-L119

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

theorem QEC.Semantics.Davies.energyProjector_adjoint (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E : ℝ) :
    LinearMap.adjoint (energyProjector b energy E) = energyProjector b energy E := by sorry
