-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorDecoupled
-- name    : QEC.Locality.exists_erasureRecovery_of_fixedGeneratorDecoupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:01.103495+00:00
-- url     : https://prove2.me/theorems/26eee9f8-b55a-4700-9461-813c8a33a60c
-- title:
--   Locality: exists erasure Recovery of fixed Generator Decoupled
-- statement:
--   Two source-decoupled regions with explicit CPTP erasure recoveries have an
--   explicit CPTP recovery after erasing their union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L440-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L440-L514

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.exists_erasureRecovery_of_fixedGeneratorDecoupled
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : FiniteSubsystem ι)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB)
    (hDecoupled : P.fixedGeneratorDecoupled (A.selected : Set ι) (B.selected : Set ι)) :
    ∃ recovery : QuantumChannel (unionSubsystem A B).complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (unionSubsystem A B).complementSystem P.semanticCode
        (unionSubsystem A B).erasureChannelFromRegister recovery := by sorry
