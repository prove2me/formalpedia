-- Prove2me | Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
-- name    : QEC.Distillation.EncodedCode.ImplementsLogicalGate.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:13:36.993911+00:00
-- url     : https://prove2.me/theorems/d0827f17-3b48-4589-99c0-7f0c709992cd
-- title:
--   Implements Logical Gate: symm
-- statement:
--   The inverse physical gate implements the inverse logical gate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean#L135-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/TransversalGate.lean#L135-L142

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

theorem QEC.Distillation.EncodedCode.ImplementsLogicalGate.symm (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) :
    E.ImplementsLogicalGate physical.symm logical.symm := by sorry
