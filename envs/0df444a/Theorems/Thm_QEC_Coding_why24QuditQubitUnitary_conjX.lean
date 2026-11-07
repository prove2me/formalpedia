-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjX
-- name    : QEC.Coding.why24QuditQubitUnitary_conjX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:51.367835+00:00
-- url     : https://prove2.me/theorems/84ff28d2-7ce2-41f7-be7b-a08cfe5418ad
-- title:
--   Coding: why24 Qudit Qubit Unitary conj X
-- statement:
--   Conjugating the actual field shift gives the concrete binary-support qubit shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L166-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L166-L178

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_conjX (β : F1024) :
    why24QuditQubitUnitary.conjOperator (why24QuditX β) =
      Semantics.Qubit.localXSupport
        (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) := by sorry
