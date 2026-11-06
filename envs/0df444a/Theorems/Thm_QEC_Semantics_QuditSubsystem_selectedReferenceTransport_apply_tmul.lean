-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
-- name    : QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:43.306589+00:00
-- url     : https://prove2.me/theorems/6c00cfeb-4786-4cda-8e33-0cf847a7136c
-- title:
--   Qudit Subsystem: selected Reference Transport apply tmul
-- statement:
--   The Qudit Subsystem construction uses the selected Reference Transport apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1020-L1024
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1020-L1024

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

theorem QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
    (global : Qudit.QuditRegister q) (ref : Ref) :
    S.selectedReferenceTransport Ref (global ⊗ₜ[Complex] ref) =
      S.selectedReferenceReordering Ref ((S.registerFactorization global) ⊗ₜ[Complex] ref) := by sorry

attribute [defeq] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
