-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_comp_projector_eq_self
-- name    : QEC.Semantics.DensityOperator.supportedOn_comp_projector_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:09.198921+00:00
-- url     : https://prove2.me/theorems/dfae0560-48b1-44ad-9166-ccc4266ced7a
-- title:
--   Density Operator: supported On comp projector eq self
-- statement:
--   The Density Operator construction uses the supported On comp projector eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L147-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L147-L150

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

theorem QEC.Semantics.DensityOperator.supportedOn_comp_projector_eq_self (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    rho.toOperator.comp C.projector = rho.toOperator := by sorry
