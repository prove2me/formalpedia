-- Prove2me | Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_maps_codeCarrier
-- name    : QEC.Distillation.EncodedCode.ImplementsLogicalGate.maps_codeCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:13:10.998069+00:00
-- url     : https://prove2.me/theorems/45b52293-50e9-49f1-9fd6-1834a71ed8d5
-- title:
--   Implements Logical Gate: maps code Carrier
-- statement:
--   Implementing a logical gate sends code vectors back into the code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean#L124-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean#L124-L132

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

theorem QEC.Distillation.EncodedCode.ImplementsLogicalGate.maps_codeCarrier (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) {x : Physical}
    (hx : x ∈ E.code.carrier) :
    physical x ∈ E.code.carrier := by sorry
