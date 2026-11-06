-- Prove2me | Theorems.Thm_QEC_Locality_inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
-- name    : QEC.Locality.inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:42.728106+00:00
-- url     : https://prove2.me/theorems/a7b3b5a0-d54d-4f31-a05f-cc5a6e39c082
-- title:
--   Locality: in Generated Group Up To Sign restrict Binary To of subset erasure correctable
-- statement:
--   Any normalizer restriction to a subset of a concretely recoverable region is generated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L385-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L385-L405

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

theorem QEC.Locality.inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι) (R : Finset ι) (hRS : R ⊆ S.selected)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer (restrictBinaryTo R E)) :
    P.code.1.InGeneratedGroupUpToSign (restrictBinaryTo R E) := by sorry
