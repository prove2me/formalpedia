-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
-- name    : QEC.Semantics.Davies.entry_diagonal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:56:07.755083+00:00
-- url     : https://prove2.me/theorems/dde365b5-0cbe-4076-91ff-8d79a022b727
-- title:
--   Davies: entry diagonal mul
-- statement:
--   The Davies construction uses the entry diagonal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L250-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L250-L254

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

theorem QEC.Semantics.Davies.entry_diagonal_mul (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (i j : ι) :
    entry b (diagonal b e * A) i j = (e i : ℂ) * entry b A i j := by sorry
