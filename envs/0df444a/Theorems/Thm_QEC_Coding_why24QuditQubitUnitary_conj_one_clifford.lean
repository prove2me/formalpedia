-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conj_one_clifford
-- name    : QEC.Coding.why24QuditQubitUnitary_conj_one_clifford
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:26:59.745511+00:00
-- url     : https://prove2.me/theorems/9bd078cd-abd4-441a-9795-f602d470f059
-- title:
--   Coding: why24 Qudit Qubit Unitary conj one clifford
-- statement:
--   Transporting the concrete field identity yields a concrete binary Clifford normalizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L432-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L432-L435

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_conj_one_clifford :
    Why24BinaryClifford
      (why24QuditQubitUnitary.conjOperator (1 : Semantics.Operator Why24QuditSpace)) := by sorry
