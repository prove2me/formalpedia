-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_toOperator_comp_projector_eq_self
-- name    : QEC.Semantics.DensityOperator.supportedOn_projector_comp_toOperator_comp_projector_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:06.821711+00:00
-- url     : https://prove2.me/theorems/cfe1ae5c-6d2f-4374-a206-978dbce5c4a2
-- title:
--   Density Operator: supported On projector comp to Operator comp projector eq self
-- statement:
--   The Density Operator construction uses the supported On projector comp to Operator comp projector eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L152-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L152-L160

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

theorem QEC.Semantics.DensityOperator.supportedOn_projector_comp_toOperator_comp_projector_eq_self
    (C : QuantumCode H) (rho : DensityOperator H) (hρ : SupportedOn C rho) :
    C.projector.comp (rho.toOperator.comp C.projector) = rho.toOperator := by sorry
