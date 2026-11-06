-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_trace_toOperator
-- name    : QEC.Semantics.DensityOperator.trace_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:41.652968+00:00
-- url     : https://prove2.me/theorems/f04f2d7f-53f0-49ce-8765-b50af0ad4b45
-- title:
--   Density Operator: trace to Operator
-- statement:
--   The Density Operator construction uses the trace to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L62-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L62-L64

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.trace_toOperator (rho : DensityOperator H) :
    LinearMap.trace Complex H rho.toOperator = 1 := by sorry
