-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_operatorSupportedOnRegister_iff_extend_restrict
-- name    : QEC.Semantics.FiniteSubsystem.operatorSupportedOnRegister_iff_extend_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:40.589612+00:00
-- url     : https://prove2.me/theorems/992a8c67-5446-4153-a9f9-931d4dc14669
-- title:
--   Finite Subsystem: operator Supported On Register iff extend restrict
-- statement:
--   The register-level restriction reconstructs exactly the selected-supported global operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L254-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L254-L262

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.operatorSupportedOnRegister_iff_extend_restrict (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) :
    S.OperatorSupportedOnRegister A ↔
      S.extendLocalToRegister (S.restrictLocalFromRegister A) = A := by sorry
