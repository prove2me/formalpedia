-- Prove2me | Theorems.Thm_QEC_Locality_erasureCorrectableFromRegister_noInformation
-- name    : QEC.Locality.erasureCorrectableFromRegister_noInformation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:43.70712+00:00
-- url     : https://prove2.me/theorems/bebc8354-fd12-4f35-9425-8819e925c2c7
-- title:
--   Locality: erasure Correctable From Register no Information
-- statement:
--   A concrete qubit erasure recovery makes the selected subsystem information-free.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L31-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L31-L40

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

theorem QEC.Locality.erasureCorrectableFromRegister_noInformation
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    (quditSubsystemOfFinite S).NoInformationOn C := by sorry
