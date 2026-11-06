-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_diagonal_apply_repr
-- name    : QEC.Semantics.Davies.diagonal_apply_repr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:45.413669+00:00
-- url     : https://prove2.me/theorems/1c5629a2-ae66-46cd-9fd8-8b0942de33d1
-- title:
--   Davies: diagonal apply repr
-- statement:
--   The Davies construction uses the diagonal apply repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L369-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L369-L379

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

theorem QEC.Semantics.Davies.diagonal_apply_repr (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (x : V) (i : ι) :
    b.repr (diagonal b e x) i = (e i : ℂ) * b.repr x i := by sorry
