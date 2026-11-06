-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_toOperator_adjoint_eq_self
-- name    : QEC.Semantics.DensityOperator.toOperator_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:50.559413+00:00
-- url     : https://prove2.me/theorems/3a8f0f25-af5d-455b-8d01-fbbcef092a0d
-- title:
--   Density Operator: to Operator adjoint eq self
-- statement:
--   The Density Operator construction uses the to Operator adjoint eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L62-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L62-L64

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

theorem QEC.Semantics.DensityOperator.toOperator_adjoint_eq_self (rho : DensityOperator H) :
    LinearMap.adjoint rho.toOperator = rho.toOperator := by sorry
