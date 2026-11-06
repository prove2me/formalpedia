-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_positive_toOperator
-- name    : QEC.Semantics.DensityOperator.positive_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:14.118422+00:00
-- url     : https://prove2.me/theorems/c1db8317-4d51-4881-be05-83614e424fd4
-- title:
--   Density Operator: positive to Operator
-- statement:
--   The Density Operator construction uses the positive to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L58-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L58-L60

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

theorem QEC.Semantics.DensityOperator.positive_toOperator (rho : DensityOperator H) :
    LinearMap.IsPositive rho.toOperator := by sorry
