-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_apply_rankOne
-- name    : QEC.Semantics.QuditSubsystem.prepareFactorized_apply_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:39.837056+00:00
-- url     : https://prove2.me/theorems/2710b462-32ae-47a1-aeaf-1bf180d4161b
-- title:
--   Qudit Subsystem: prepare Factorized apply rank One
-- statement:
--   The Qudit Subsystem construction uses the prepare Factorized apply rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L174-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L174-L188

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

theorem QEC.Semantics.QuditSubsystem.prepareFactorized_apply_rankOne (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (k l : S.complementSystem) :
    S.prepareFactorized rho
        (InnerProductSpace.rankOne Complex k l).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (S.densityEnsembleVectors rho i ⊗ₜ[Complex] k)
        (S.densityEnsembleVectors rho i ⊗ₜ[Complex] l)).toLinearMap := by sorry
