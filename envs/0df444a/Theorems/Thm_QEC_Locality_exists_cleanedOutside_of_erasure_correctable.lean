-- Prove2me | Theorems.Thm_QEC_Locality_exists_cleanedOutside_of_erasure_correctable
-- name    : QEC.Locality.exists_cleanedOutside_of_erasure_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:49.495115+00:00
-- url     : https://prove2.me/theorems/68d69024-39aa-4d6c-aa4e-e99b9e3f5b38
-- title:
--   Locality: exists cleaned Outside of erasure correctable
-- statement:
--   Concrete erasure recovery gives the stabilizer cleaning decomposition: every
--   normalizer representative differs from one supported outside the recovered region
--   by an actual generated-stabilizer vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L244-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L244-L290

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

theorem QEC.Locality.exists_cleanedOutside_of_erasure_correctable
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer E) :
    ∃ s, s ∈ P.code.1.generatedVectorSubspace ∧
      ∃ outside : Binary ι,
        P.code.1.InBinaryNormalizer outside ∧
        support outside ⊆ S.selectedᶜ ∧
        E.vector = s + outside.vector := by sorry
