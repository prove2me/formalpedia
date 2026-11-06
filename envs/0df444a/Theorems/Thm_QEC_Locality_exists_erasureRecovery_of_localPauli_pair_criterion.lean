-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_localPauli_pair_criterion
-- name    : QEC.Locality.exists_erasureRecovery_of_localPauli_pair_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:45.181208+00:00
-- url     : https://prove2.me/theorems/78c13103-1982-44a0-9824-71b6b9628d04
-- title:
--   Locality: exists erasure Recovery of local Pauli pair criterion
-- statement:
--   The Locality construction uses the exists erasure Recovery of local Pauli pair criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L516-L554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L516-L554

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

theorem QEC.Locality.exists_erasureRecovery_of_localPauli_pair_criterion
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (hPairs : ∀ p q : LocalPauliWordIndex S,
      localPauliAmplitude S ≠ 0 → localPauliAmplitude S ≠ 0 →
        P.code.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q)) ∨
          ¬ P.code.1.InBinaryNormalizer
            (binaryMul (binaryDagger (embeddedLocalPauli S p))
              (embeddedLocalPauli S q))) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
        S.erasureChannelFromRegister recovery := by sorry
