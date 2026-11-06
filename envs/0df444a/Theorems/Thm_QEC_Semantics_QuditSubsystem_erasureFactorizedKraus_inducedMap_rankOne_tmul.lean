-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureFactorizedKraus_inducedMap_rankOne_tmul
-- name    : QEC.Semantics.QuditSubsystem.erasureFactorizedKraus_inducedMap_rankOne_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:33.126192+00:00
-- url     : https://prove2.me/theorems/1903cfcb-c102-4802-bde4-f4af1d6012c5
-- title:
--   Qudit Subsystem: erasure Factorized Kraus induced Map rank One tmul
-- statement:
--   The Qudit Subsystem construction uses the erasure Factorized Kraus induced Map rank One tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L356-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L356-L416

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.erasureFactorizedKraus_inducedMap_rankOne_tmul
    (S : QuditSubsystem q) (h h' : S.selectedSystem)
    (k k' : S.complementSystem) :
    S.erasureFactorizedKraus.inducedMap
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by sorry
