-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_iff_projector_comp_eq
-- name    : QEC.Semantics.DensityOperator.supportedOn_iff_projector_comp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:30.057206+00:00
-- url     : https://prove2.me/theorems/bf07dcd9-db94-485d-9b55-a8f8228314f2
-- title:
--   Density Operator: supported On iff projector comp eq
-- statement:
--   The Density Operator construction uses the supported On iff projector comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L116-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L116-L125

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

theorem QEC.Semantics.DensityOperator.supportedOn_iff_projector_comp_eq (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ C.projector.comp rho.toOperator = rho.toOperator := by sorry
