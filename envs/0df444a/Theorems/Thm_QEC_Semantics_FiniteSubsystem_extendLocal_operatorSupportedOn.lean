-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_operatorSupportedOn
-- name    : QEC.Semantics.FiniteSubsystem.extendLocal_operatorSupportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:09.82159+00:00
-- url     : https://prove2.me/theorems/3ee85252-aff2-44c4-bb91-6b3ccf6c4830
-- title:
--   Finite Subsystem: extend Local operator Supported On
-- statement:
--   The Finite Subsystem construction uses the extend Local operator Supported On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L233-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L233-L236

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

theorem QEC.Semantics.FiniteSubsystem.extendLocal_operatorSupportedOn (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOn (S.extendLocal A) := by sorry
