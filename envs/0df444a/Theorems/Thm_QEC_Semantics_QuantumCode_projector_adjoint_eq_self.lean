-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
-- name    : QEC.Semantics.QuantumCode.projector_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:07.364057+00:00
-- url     : https://prove2.me/theorems/06f0fe18-7990-48bf-bdfb-8020f96ad328
-- title:
--   Quantum Code: projector adjoint eq self
-- statement:
--   The Quantum Code construction uses the projector adjoint eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L51-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L51-L53

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.QuantumCode.projector_adjoint_eq_self (C : QuantumCode H) :
    LinearMap.adjoint C.projector = C.projector := by sorry
