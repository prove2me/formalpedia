-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_adjoint_comp
-- name    : QEC.Semantics.QuditSubsystem.erasureKraus_adjoint_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:51.243596+00:00
-- url     : https://prove2.me/theorems/422f5b87-a418-436b-8811-5247f9423b71
-- title:
--   Qudit Subsystem: erasure Kraus adjoint comp
-- statement:
--   The Qudit Subsystem construction uses the erasure Kraus adjoint comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L476-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L476-L506

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

theorem QEC.Semantics.QuditSubsystem.erasureKraus_adjoint_comp (S : QuditSubsystem q)
    (i j : Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.erasureKraus).operator i)).comp
      ((S.erasureKraus).operator j) =
      S.extendLocalToRegister (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex S.selectedSystem) i)
        ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap := by sorry
