-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_projector_apply
-- name    : QEC.Semantics.QuantumCode.projector_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:23.954516+00:00
-- url     : https://prove2.me/theorems/7e317fa7-74d9-405d-9436-e8f2a7241c1e
-- title:
--   Quantum Code: projector apply
-- statement:
--   The Quantum Code construction uses the projector apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L26-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L26-L28

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

theorem QEC.Semantics.QuantumCode.projector_apply (C : QuantumCode H) (v : H) :
    C.projector v = C.carrier.starProjection v := by sorry
