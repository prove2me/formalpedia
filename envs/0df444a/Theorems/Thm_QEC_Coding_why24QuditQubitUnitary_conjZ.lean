-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjZ
-- name    : QEC.Coding.why24QuditQubitUnitary_conjZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:45.260602+00:00
-- url     : https://prove2.me/theorems/6f8bfc7e-0945-4059-9608-dff41a950923
-- title:
--   Coding: why24 Qudit Qubit Unitary conj Z
-- statement:
--   Conjugating the actual field trace phase gives the concrete binary-support qubit phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L227-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L227-L258

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_conjZ (γ : F1024) :
    why24QuditQubitUnitary.conjOperator (why24QuditZ γ) =
      Semantics.Qubit.localZSupport
        (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) := by sorry
