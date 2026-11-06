-- Prove2me | Theorems.Thm_QEC_Semantics_selfAdjointTraceNormOneToOne_nonneg
-- name    : QEC.Semantics.selfAdjointTraceNormOneToOne_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:29:33.989471+00:00
-- url     : https://prove2.me/theorems/f4474856-ee6c-46ce-b42c-89230e28c1e0
-- title:
--   Semantics: self Adjoint Trace Norm One To One nonneg
-- statement:
--   The Semantics construction uses the self Adjoint Trace Norm One To One nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L92-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L92-L100

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.selfAdjointTraceNormOneToOne_nonneg (L : Superoperator H) :
    0 ≤ selfAdjointTraceNormOneToOne L := by sorry
