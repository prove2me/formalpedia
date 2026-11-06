-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_rankOne_tmul
-- name    : QEC.Semantics.QuditSubsystem.erasureChannel_rankOne_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:26.135183+00:00
-- url     : https://prove2.me/theorems/9a1356c6-2737-44f9-8df9-6ccb8d136a08
-- title:
--   Qudit Subsystem: erasure Channel rank One tmul
-- statement:
--   The concrete factored erasure channel contracts the selected tensor factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1056-L1066
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1056-L1066

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

theorem QEC.Semantics.QuditSubsystem.erasureChannel_rankOne_tmul (S : QuditSubsystem q)
    (h h' : S.selectedSystem) (k k' : S.complementSystem) :
    S.erasureChannel
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by sorry
