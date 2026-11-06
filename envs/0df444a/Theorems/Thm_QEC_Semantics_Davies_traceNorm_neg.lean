-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_traceNorm_neg
-- name    : QEC.Semantics.Davies.traceNorm_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:40.363404+00:00
-- url     : https://prove2.me/theorems/a1837879-d0e1-45f8-978b-d4ee333bfdec
-- title:
--   Davies: trace Norm neg
-- statement:
--   The Davies construction uses the trace Norm neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L40-L42

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem QEC.Semantics.Davies.traceNorm_neg (F : Operator V) : traceNorm (-F) = traceNorm F := by sorry
