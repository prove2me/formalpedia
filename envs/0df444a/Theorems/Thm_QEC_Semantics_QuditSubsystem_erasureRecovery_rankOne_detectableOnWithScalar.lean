-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_rankOne_detectableOnWithScalar
-- name    : QEC.Semantics.QuditSubsystem.erasureRecovery_rankOne_detectableOnWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:26.996266+00:00
-- url     : https://prove2.me/theorems/2e3351f4-e5c7-4311-8e9a-645e7c01703d
-- title:
--   Qudit Subsystem: erasure Recovery rank One detectable On With Scalar
-- statement:
--   The Qudit Subsystem construction uses the erasure Recovery rank One detectable On With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L541-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L541-L570

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

theorem QEC.Semantics.QuditSubsystem.erasureRecovery_rankOne_detectableOnWithScalar (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (i j : Fin (Module.finrank Complex S.selectedSystem)) :
    ∃ scalar : Complex,
      DetectableOnWithScalar C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) i)
          ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap)
        scalar := by sorry
