-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith
-- name    : QEC.Semantics.QuditSubsystem.replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:55.478819+00:00
-- url     : https://prove2.me/theorems/f196fe1b-8079-41bc-8a7c-1cd5238bfcf8
-- title:
--   Qudit Subsystem: replacement Kraus to Quantum Channel eq replacement After Erasure With
-- statement:
--   The Qudit Subsystem construction uses the replacement Kraus to Quantum Channel eq replacement After Erasure With property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1179-L1196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1179-L1196

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
set_option maxRecDepth 4096

theorem QEC.Semantics.QuditSubsystem.replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (hComplete : (S.replacementKraus rho).Complete) :
    (S.replacementKraus rho).toQuantumChannel hComplete =
      S.replacementAfterErasureWith rho := by sorry
