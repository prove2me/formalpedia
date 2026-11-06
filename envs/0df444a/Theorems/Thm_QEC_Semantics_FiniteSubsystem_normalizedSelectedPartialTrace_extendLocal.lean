-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_normalizedSelectedPartialTrace_extendLocal
-- name    : QEC.Semantics.FiniteSubsystem.normalizedSelectedPartialTrace_extendLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:36.779418+00:00
-- url     : https://prove2.me/theorems/c6a2f6bf-5c02-4ac0-ad5f-dcb84cec5870
-- title:
--   Finite Subsystem: normalized Selected Partial Trace extend Local
-- statement:
--   The normalized selected partial trace recovers an identity-extended local operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L319-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L319-L327

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

theorem QEC.Semantics.FiniteSubsystem.normalizedSelectedPartialTrace_extendLocal (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.normalizedSelectedPartialTrace (S.extendLocal A) = A := by sorry
