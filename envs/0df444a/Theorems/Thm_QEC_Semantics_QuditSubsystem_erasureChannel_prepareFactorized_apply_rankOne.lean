-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_prepareFactorized_apply_rankOne
-- name    : QEC.Semantics.QuditSubsystem.erasureChannel_prepareFactorized_apply_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:53.064235+00:00
-- url     : https://prove2.me/theorems/d9ef99b8-3ebd-49ce-8a71-bdecb71d4ea2
-- title:
--   Qudit Subsystem: erasure Channel prepare Factorized apply rank One
-- statement:
--   The Qudit Subsystem construction uses the erasure Channel prepare Factorized apply rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L190-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L190-L200

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

theorem QEC.Semantics.QuditSubsystem.erasureChannel_prepareFactorized_apply_rankOne (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (k l : S.complementSystem) :
    S.erasureChannel
      (S.prepareFactorized rho (InnerProductSpace.rankOne Complex k l).toLinearMap) =
      (InnerProductSpace.rankOne Complex k l).toLinearMap := by sorry
