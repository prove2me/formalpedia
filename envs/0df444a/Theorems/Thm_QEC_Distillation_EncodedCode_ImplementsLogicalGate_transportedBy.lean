-- Prove2me | Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_transportedBy
-- name    : QEC.Distillation.EncodedCode.ImplementsLogicalGate.transportedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:27.433949+00:00
-- url     : https://prove2.me/theorems/bb7473ce-264a-4ffe-953d-eac1ad3f3315
-- title:
--   Implements Logical Gate: transported By
-- statement:
--   Exact logical implementation implies two-sided preservation of the code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean#L145-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean#L145-L155

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_Core_TransversalGate
set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
variable {Logical Physical Site : Type u}
variable [NormedAddCommGroup Logical] [InnerProductSpace Complex Logical]
variable [FiniteQuantumSystem Logical]
variable [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
variable [FiniteQuantumSystem Physical]
open QEC.Distillation.EncodedCode
open QEC.Distillation.EncodedCode.ImplementsLogicalGate

theorem QEC.Distillation.EncodedCode.ImplementsLogicalGate.transportedBy (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) :
    QuantumCode.TransportedBy physical E.code E.code := by sorry
