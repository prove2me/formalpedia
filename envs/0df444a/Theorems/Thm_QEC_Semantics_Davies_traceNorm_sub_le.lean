-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_traceNorm_sub_le
-- name    : QEC.Semantics.Davies.traceNorm_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:04:02.400203+00:00
-- url     : https://prove2.me/theorems/ca5f7a10-cb0c-483b-87cc-81022d990eeb
-- title:
--   Davies: trace Norm sub le
-- statement:
--   The Davies construction uses the trace Norm sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L44-L46

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem QEC.Semantics.Davies.traceNorm_sub_le (F G : Operator V) :
    traceNorm (F-G) ≤ traceNorm F + traceNorm G := by sorry
