-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_mul
-- name    : QEC.Semantics.Davies.entry_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:55:48.23219+00:00
-- url     : https://prove2.me/theorems/9cf03813-a765-4972-b788-c96ec555cb4d
-- title:
--   Davies: entry mul
-- statement:
--   The Davies construction uses the entry mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L57-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L57-L64

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

theorem QEC.Semantics.Davies.entry_mul (b : OrthonormalBasis ι ℂ V) (A B : Operator V) (i j : ι) :
    entry b (A * B) i j = ∑ k, entry b A i k * entry b B k j := by sorry
