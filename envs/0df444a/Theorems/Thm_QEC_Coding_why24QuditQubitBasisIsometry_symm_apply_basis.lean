-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitBasisIsometry_symm_apply_basis
-- name    : QEC.Coding.why24QuditQubitBasisIsometry_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:26:46.156272+00:00
-- url     : https://prove2.me/theorems/3e69c088-14f5-481d-890e-4a09701f0bbe
-- title:
--   Coding: why24 Qudit Qubit Basis Isometry symm apply basis
-- statement:
--   Reverse action on every ten-qubit computational-basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L58-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L58-L65

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitBasisIsometry_symm_apply_basis
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24QuditQubitBasisIsometry.symm (why24QubitComputationalBasis bits) =
      why24QuditComputationalBasis (why24ComputationalLabelEquiv.symm bits) := by sorry
