-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_matrixElement_scalars
-- name    : QEC.Semantics.QuditSubsystem.erasureRecovery_matrixElement_scalars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:26.484227+00:00
-- url     : https://prove2.me/theorems/34b12b9f-46b2-4103-bc62-1e9d0ceff786
-- title:
--   Qudit Subsystem: erasure Recovery matrix Element scalars
-- statement:
--   The Qudit Subsystem construction uses the erasure Recovery matrix Element scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L509-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L509-L538

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

theorem QEC.Semantics.QuditSubsystem.erasureRecovery_matrixElement_scalars (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    ∃ scalar : Fin (Module.finrank Complex S.selectedSystem) →
        Fin (Module.finrank Complex S.selectedSystem) → Complex,
      ∀ i j (x : Qudit.QuditRegister q), x ∈ C.carrier →
        ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
          inner Complex ((S.erasureKraus).operator i x)
            ((S.erasureKraus).operator j y) =
              scalar i j * inner Complex x y := by sorry
