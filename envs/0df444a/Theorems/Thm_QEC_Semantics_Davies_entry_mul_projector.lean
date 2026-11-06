-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_mul_projector
-- name    : QEC.Semantics.Davies.entry_mul_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:21.671358+00:00
-- url     : https://prove2.me/theorems/4d544b0f-040f-4760-af6f-2050faa995a6
-- title:
--   Davies: entry mul projector
-- statement:
--   The Davies construction uses the entry mul projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L456-L464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L456-L464

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

theorem QEC.Semantics.Davies.entry_mul_projector (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (E : ℝ) (A : Operator V) (i j : ι) :
    entry b (A * energyProjector b e E) i j = if e j = E then entry b A i j else 0 := by sorry
