-- Prove2me | Theorems.Thm_QEC_Locality_detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
-- name    : QEC.Locality.detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:10:56.672342+00:00
-- url     : https://prove2.me/theorems/29031113-30f6-4701-84c3-08100a6d8fb8
-- title:
--   Locality: detectable On embedded Local Pauli of erasure Correctable From Register
-- statement:
--   A local Pauli branch is detectable after concrete recovery from its erasure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L43-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L43-L57

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem C
      S.erasureChannelFromRegister recovery) (p : LocalPauliWordIndex S) :
    DetectableOn C (toQubitOperator (embeddedLocalPauli S p)) := by sorry
