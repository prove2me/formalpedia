-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_operatorSupportedOn_iff_extend_restrict
-- name    : QEC.Semantics.FiniteSubsystem.operatorSupportedOn_iff_extend_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:18.132835+00:00
-- url     : https://prove2.me/theorems/0fe8d622-56cd-40cb-8b9e-700cb981d415
-- title:
--   Finite Subsystem: operator Supported On iff extend restrict
-- statement:
--   The concrete restriction reconstructs exactly the operators supported on the selected system.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L244-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L244-L251

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

theorem QEC.Semantics.FiniteSubsystem.operatorSupportedOn_iff_extend_restrict (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) :
    S.OperatorSupportedOn A ↔ S.extendLocal (S.restrictLocal A) = A := by sorry
