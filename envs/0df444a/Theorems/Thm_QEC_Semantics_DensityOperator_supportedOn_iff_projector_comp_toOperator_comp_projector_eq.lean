-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_iff_projector_comp_toOperator_comp_projector_eq
-- name    : QEC.Semantics.DensityOperator.supportedOn_iff_projector_comp_toOperator_comp_projector_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:52.523708+00:00
-- url     : https://prove2.me/theorems/06f7e789-1c25-4101-a2ab-76f8d2e1c8fb
-- title:
--   Density Operator: supported On iff projector comp to Operator comp projector eq
-- statement:
--   The Density Operator construction uses the supported On iff projector comp to Operator comp projector eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L162-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L162-L172

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

theorem QEC.Semantics.DensityOperator.supportedOn_iff_projector_comp_toOperator_comp_projector_eq
    (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ C.projector.comp (rho.toOperator.comp C.projector) = rho.toOperator := by sorry
