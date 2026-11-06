-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
-- name    : QEC.Semantics.QuantumCode.projector_eq_self_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:09.257118+00:00
-- url     : https://prove2.me/theorems/6a05b7fc-1ae2-4314-969c-1fc7b2191b82
-- title:
--   Quantum Code: projector eq self of mem
-- statement:
--   The Quantum Code construction uses the projector eq self of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L38-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L38-L40

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

theorem QEC.Semantics.QuantumCode.projector_eq_self_of_mem (C : QuantumCode H) {v : H} (hv : v ∈ C.carrier) :
    C.projector v = v := by sorry
