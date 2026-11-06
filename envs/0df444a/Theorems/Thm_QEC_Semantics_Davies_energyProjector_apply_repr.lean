-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_apply_repr
-- name    : QEC.Semantics.Davies.energyProjector_apply_repr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:06.649462+00:00
-- url     : https://prove2.me/theorems/640a81ea-9001-47d9-bdbb-5519367b2762
-- title:
--   Davies: energy Projector apply repr
-- statement:
--   The Davies construction uses the energy Projector apply repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L381-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L381-L393

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

theorem QEC.Semantics.Davies.energyProjector_apply_repr (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (E : ℝ) (x : V) (i : ι) :
    b.repr (energyProjector b e E x) i = if e i = E then b.repr x i else 0 := by sorry
