-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_projector_mul
-- name    : QEC.Semantics.Davies.entry_projector_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:05.646205+00:00
-- url     : https://prove2.me/theorems/0d93da38-3e93-4d91-8e68-c262ed954ac0
-- title:
--   Davies: entry projector mul
-- statement:
--   The Davies construction uses the entry projector mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L446-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L446-L454

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

theorem QEC.Semantics.Davies.entry_projector_mul (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (E : ℝ) (A : Operator V) (i j : ι) :
    entry b (energyProjector b e E * A) i j = if e i = E then entry b A i j else 0 := by sorry
