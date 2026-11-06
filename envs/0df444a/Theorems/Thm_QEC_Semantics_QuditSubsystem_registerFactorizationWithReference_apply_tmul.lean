-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
-- name    : QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:39.347142+00:00
-- url     : https://prove2.me/theorems/0d8d3e73-b391-44c9-88eb-5ccec8b287ee
-- title:
--   Qudit Subsystem: register Factorization With Reference apply tmul
-- statement:
--   The Qudit Subsystem construction uses the register Factorization With Reference apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L999-L1003
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L999-L1003

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
variable (S : QuditSubsystem q)
variable (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]

theorem QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
    (global : Qudit.QuditRegister q) (ref : Ref) :
    S.registerFactorizationWithReference Ref (global ⊗ₜ[Complex] ref) =
      (S.registerFactorization global) ⊗ₜ[Complex] ref := by sorry

attribute [defeq] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
