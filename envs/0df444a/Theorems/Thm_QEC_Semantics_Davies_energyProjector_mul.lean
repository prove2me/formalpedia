-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_mul
-- name    : QEC.Semantics.Davies.energyProjector_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:03:47.084548+00:00
-- url     : https://prove2.me/theorems/300fb223-d4c4-42b5-bfd0-a5d9780d7c99
-- title:
--   Davies: energy Projector mul
-- statement:
--   The Davies construction uses the energy Projector mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L121-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L121-L131

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

theorem QEC.Semantics.Davies.energyProjector_mul (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E F : ℝ) :
    energyProjector b energy E * energyProjector b energy F =
      if E = F then energyProjector b energy E else 0 := by sorry
