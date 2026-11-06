-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_rankOne_tmul_reference
-- name    : QEC.Semantics.QuditSubsystem.erasureChannel_rankOne_tmul_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:41.754208+00:00
-- url     : https://prove2.me/theorems/94f1a4a3-868a-46e4-9919-2a03b3c756c5
-- title:
--   Qudit Subsystem: erasure Channel rank One tmul reference
-- statement:
--   The Qudit Subsystem construction uses the erasure Channel rank One tmul reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L419-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L419-L429

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

theorem QEC.Semantics.QuditSubsystem.erasureChannel_rankOne_tmul_reference (S : QuditSubsystem q)
    (h h' : S.selectedSystem) (k k' : S.complementSystem) :
    S.erasureChannel
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by sorry
