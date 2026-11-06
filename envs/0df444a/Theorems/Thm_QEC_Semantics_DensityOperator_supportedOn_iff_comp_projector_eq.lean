-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_iff_comp_projector_eq
-- name    : QEC.Semantics.DensityOperator.supportedOn_iff_comp_projector_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:12.844611+00:00
-- url     : https://prove2.me/theorems/e0fc0db8-1920-4010-a446-5b7a40c2d889
-- title:
--   Density Operator: supported On iff comp projector eq
-- statement:
--   The Density Operator construction uses the supported On iff comp projector eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L132-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L132-L145

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

theorem QEC.Semantics.DensityOperator.supportedOn_iff_comp_projector_eq (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ rho.toOperator.comp C.projector = rho.toOperator := by sorry
