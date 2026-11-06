-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
-- name    : QEC.Semantics.QuantumCode.projector_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:23.294372+00:00
-- url     : https://prove2.me/theorems/650fdcd0-d14d-4e13-b9f2-e743784b59b3
-- title:
--   Quantum Code: projector mem carrier
-- statement:
--   The Quantum Code construction uses the projector mem carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L30-L32

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

theorem QEC.Semantics.QuantumCode.projector_mem_carrier (C : QuantumCode H) (v : H) :
    C.projector v ∈ C.carrier := by sorry
