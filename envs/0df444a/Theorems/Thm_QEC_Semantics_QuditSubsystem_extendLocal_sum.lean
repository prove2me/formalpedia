-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_sum
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:56.424768+00:00
-- url     : https://prove2.me/theorems/8cf99a5f-eb0a-4a83-8501-228c8e923c9d
-- title:
--   Qudit Subsystem: extend Local sum
-- statement:
--   Factorized local extension preserves finite sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L712-L719
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L712-L719

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.extendLocal_sum (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocal (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocal (f i) := by sorry
