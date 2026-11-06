-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
-- name    : QEC.Semantics.DensityOperator.pureOfNonzero_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:00:53.925433+00:00
-- url     : https://prove2.me/theorems/151b6ab8-6e47-457d-896c-d25644e90e3c
-- title:
--   Density Operator: pure Of Nonzero apply
-- statement:
--   The Density Operator construction uses the pure Of Nonzero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L97-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L97-L100

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.pureOfNonzero_apply (x y : H) (hx : x ≠ 0) :
    (pureOfNonzero x hx).toOperator y =
      ((inner Complex x x)⁻¹ * inner Complex x y) • x := by sorry
