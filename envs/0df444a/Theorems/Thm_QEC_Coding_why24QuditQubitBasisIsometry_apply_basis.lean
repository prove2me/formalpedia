-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitBasisIsometry_apply_basis
-- name    : QEC.Coding.why24QuditQubitBasisIsometry_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:22.433542+00:00
-- url     : https://prove2.me/theorems/d8ba0ec0-85fc-4fd0-bffa-b60ab8f2d2eb
-- title:
--   Coding: why24 Qudit Qubit Basis Isometry apply basis
-- statement:
--   Forward action on every concrete `F1024` computational-basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L52-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L52-L55

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitBasisIsometry_apply_basis (β : F1024) :
    why24QuditQubitBasisIsometry (why24QuditComputationalBasis β) =
      why24QubitComputationalBasis (why24ComputationalLabelEquiv β) := by sorry
