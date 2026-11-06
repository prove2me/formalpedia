-- Prove2me | Theorems.Thm_QEC_Locality_two_correctable_regions_encodedQubits_le_separator_card
-- name    : QEC.Locality.two_correctable_regions_encodedQubits_le_separator_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:11:43.513736+00:00
-- url     : https://prove2.me/theorems/36eeacb0-cde2-4809-905e-afca7c0f8dda
-- title:
--   Locality: two correctable regions encoded Qubits le separator card
-- statement:
--   For a finite faithful stabilizer presentation, exact recovery from erasure of
--   two disjoint regions bounds the encoded logical dimension by the remaining
--   region's qubit count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L315-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L315-L352

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

theorem QEC.Locality.two_correctable_regions_encodedQubits_le_separator_card
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B C : FiniteSubsystem ι)
    (hAB : Disjoint A.selected B.selected)
    (hAC : Disjoint A.selected C.selected)
    (hBC : Disjoint B.selected C.selected)
    (hCover : A.selected ∪ B.selected ∪ C.selected = Finset.univ)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB) :
    P.encodedQubits ≤ C.selected.card := by sorry
