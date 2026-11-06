-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_prepareFactorized_apply
-- name    : QEC.Semantics.QuditSubsystem.erasureChannel_prepareFactorized_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:41.505088+00:00
-- url     : https://prove2.me/theorems/1170a21e-36c2-481a-bea1-2620bb1165ff
-- title:
--   Qudit Subsystem: erasure Channel prepare Factorized apply
-- statement:
--   The Qudit Subsystem construction uses the erasure Channel prepare Factorized apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L202-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L202-L210

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.erasureChannel_prepareFactorized_apply (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (A : Operator S.complementSystem) :
    S.erasureChannel (S.prepareFactorized rho A) = A := by sorry
