-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_adjoint
-- name    : QEC.Semantics.Davies.entry_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:57:15.739792+00:00
-- url     : https://prove2.me/theorems/16e635bc-405e-48c2-b7e5-d46f00e6199c
-- title:
--   Davies: entry adjoint
-- statement:
--   The Davies construction uses the entry adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L66-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L66-L69

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

theorem QEC.Semantics.Davies.entry_adjoint (b : OrthonormalBasis ι ℂ V) (A : Operator V) (i j : ι) :
    entry b (LinearMap.adjoint A) i j = star (entry b A j i) := by sorry
