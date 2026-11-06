-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
-- name    : QEC.Locality.exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:00:55.288589+00:00
-- url     : https://prove2.me/theorems/e6a0b122-c94b-402f-b83a-8810baf7e3d2
-- title:
--   Locality: exists erasure Recovery of pairwise fixed Generator Decoupled
-- statement:
--   The Locality construction uses the exists erasure Recovery of pairwise fixed Generator Decoupled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L680-L759
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L680-L759

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

theorem QEC.Locality.exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
    {κ : Type v} [Fintype κ] {α : Type w} [DecidableEq α]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (regions : α → FiniteSubsystem ι) (s : Finset α)
    (hRecovery : ∀ a, a ∈ s →
      ∃ recovery : QuantumChannel (regions a).complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) (regions a).complementSystem P.semanticCode
          (regions a).erasureChannelFromRegister recovery)
    (hDecoupled : ∀ a, a ∈ s → ∀ b, b ∈ s → a ≠ b →
      P.fixedGeneratorDecoupled ((regions a).selected : Set ι) ((regions b).selected : Set ι)) :
    ∃ recovery : QuantumChannel (familyUnionSubsystem regions s).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (familyUnionSubsystem regions s).complementSystem
        P.semanticCode (familyUnionSubsystem regions s).erasureChannelFromRegister recovery := by sorry
