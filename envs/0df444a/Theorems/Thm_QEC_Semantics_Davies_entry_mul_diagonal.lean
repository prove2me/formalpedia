-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
-- name    : QEC.Semantics.Davies.entry_mul_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:54:55.965113+00:00
-- url     : https://prove2.me/theorems/4a2c6969-ba0c-4a5c-925c-2cadae12827c
-- title:
--   Davies: entry mul diagonal
-- statement:
--   The Davies construction uses the entry mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L256-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L256-L260

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

theorem QEC.Semantics.Davies.entry_mul_diagonal (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (i j : ι) :
    entry b (A * diagonal b e) i j = entry b A i j * (e j : ℂ) := by sorry
