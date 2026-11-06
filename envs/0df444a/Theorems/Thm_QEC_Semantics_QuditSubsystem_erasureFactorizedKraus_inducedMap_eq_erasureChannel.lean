-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureFactorizedKraus_inducedMap_eq_erasureChannel
-- name    : QEC.Semantics.QuditSubsystem.erasureFactorizedKraus_inducedMap_eq_erasureChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:18.046636+00:00
-- url     : https://prove2.me/theorems/cc6d7872-1a5e-410c-afe7-daa705f91553
-- title:
--   Qudit Subsystem: erasure Factorized Kraus induced Map eq erasure Channel
-- statement:
--   The Qudit Subsystem construction uses the erasure Factorized Kraus induced Map eq erasure Channel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L432-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L432-L444

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

theorem QEC.Semantics.QuditSubsystem.erasureFactorizedKraus_inducedMap_eq_erasureChannel (S : QuditSubsystem q) :
    S.erasureFactorizedKraus.inducedMap = S.erasureChannel.toLinearMap := by sorry
