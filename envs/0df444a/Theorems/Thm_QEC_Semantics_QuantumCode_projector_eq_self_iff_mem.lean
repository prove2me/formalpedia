-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_iff_mem
-- name    : QEC.Semantics.QuantumCode.projector_eq_self_iff_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:26.022226+00:00
-- url     : https://prove2.me/theorems/a160dd8a-7ef2-4c84-a531-f453a2cfc526
-- title:
--   Quantum Code: projector eq self iff mem
-- statement:
--   The Quantum Code construction uses the projector eq self iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L34-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L34-L36

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

theorem QEC.Semantics.QuantumCode.projector_eq_self_iff_mem (C : QuantumCode H) {v : H} :
    C.projector v = v ↔ v ∈ C.carrier := by sorry
