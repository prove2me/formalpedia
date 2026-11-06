-- Prove2me | Theorems.Thm_QEC_Locality_generatorRank_ge_two_correctable_region_cards
-- name    : QEC.Locality.generatorRank_ge_two_correctable_region_cards
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:48.320189+00:00
-- url     : https://prove2.me/theorems/8abac339-23fd-4c72-a50d-7225b9f7b66f
-- title:
--   Locality: generator Rank ge two correctable region cards
-- statement:
--   Two disjoint recoverable regions force the actual stabilizer rank to cover both.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L265-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L265-L308

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

theorem QEC.Locality.generatorRank_ge_two_correctable_region_cards
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : FiniteSubsystem ι)
    (hDisjoint : Disjoint A.selected B.selected)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB) :
    A.selected.card + B.selected.card ≤ P.generatorRank := by sorry
