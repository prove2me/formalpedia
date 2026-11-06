-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_eq_projector_sum
-- name    : QEC.Semantics.Davies.frequencyComponent_eq_projector_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:34.710546+00:00
-- url     : https://prove2.me/theorems/257d2840-ac09-4388-b695-2c54605f3345
-- title:
--   Davies: frequency Component eq projector sum
-- statement:
--   Equal-frequency blocks are summed before constructing any quadratic jump.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L484-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L484-L489

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

theorem QEC.Semantics.Davies.frequencyComponent_eq_projector_sum (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (ω : ℝ) :
    frequencyComponent b e A ω = ∑ E ∈ energyValues e, ∑ F ∈ energyValues e,
      if F-E = ω then energyProjector b e E * A * energyProjector b e F else 0 := by sorry
