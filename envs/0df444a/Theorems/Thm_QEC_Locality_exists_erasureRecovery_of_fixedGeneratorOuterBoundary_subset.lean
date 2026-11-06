-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
-- name    : QEC.Locality.exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:00:43.917755+00:00
-- url     : https://prove2.me/theorems/d282bcb0-2cf4-4675-812e-c7902a396eea
-- title:
--   Locality: exists erasure Recovery of fixed Generator Outer Boundary subset
-- statement:
--   Two concretely erasure-correctable regions remain concretely correctable after
--   union when the second contains the first region's fixed-generator outer boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L566-L673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L566-L673

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

theorem QEC.Locality.exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (U T : FiniteSubsystem ι)
    (recoveryU : QuantumChannel U.complementSystem (Qubit.QubitRegister ι))
    (recoveryT : QuantumChannel T.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryU : Correctable (Qubit.QubitRegister ι) U.complementSystem P.semanticCode
      U.erasureChannelFromRegister recoveryU)
    (hRecoveryT : Correctable (Qubit.QubitRegister ι) T.complementSystem P.semanticCode
      T.erasureChannelFromRegister recoveryT)
    (hBoundary : P.fixedGeneratorOuterBoundary (U.selected : Set ι) ⊆
      (T.selected : Set ι)) :
    ∃ recovery : QuantumChannel (unionSubsystem U T).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (unionSubsystem U T).complementSystem
        P.semanticCode (unionSubsystem U T).erasureChannelFromRegister recovery := by sorry
