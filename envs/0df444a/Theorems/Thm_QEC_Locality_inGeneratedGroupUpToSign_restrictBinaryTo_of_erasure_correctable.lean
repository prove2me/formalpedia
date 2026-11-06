-- Prove2me | Theorems.Thm_QEC_Locality_inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
-- name    : QEC.Locality.inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:51.376169+00:00
-- url     : https://prove2.me/theorems/c877acf5-b95f-4eca-b0a6-7ff0ed2d341a
-- title:
--   Locality: in Generated Group Up To Sign restrict Binary To of erasure correctable
-- statement:
--   The Locality construction uses the in Generated Group Up To Sign restrict Binary To of erasure correctable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L369-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L369-L382

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

theorem QEC.Locality.inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer (restrictBinaryTo S.selected E)) :
    P.code.1.InGeneratedGroupUpToSign (restrictBinaryTo S.selected E) := by sorry
