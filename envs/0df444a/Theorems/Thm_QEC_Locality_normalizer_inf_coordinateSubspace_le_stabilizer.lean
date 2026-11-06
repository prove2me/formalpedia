-- Prove2me | Theorems.Thm_QEC_Locality_normalizer_inf_coordinateSubspace_le_stabilizer
-- name    : QEC.Locality.normalizer_inf_coordinateSubspace_le_stabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:56.925946+00:00
-- url     : https://prove2.me/theorems/4a466143-0ec4-4334-b4a1-16f0631d8ab1
-- title:
--   Locality: normalizer inf coordinate Subspace le stabilizer
-- statement:
--   Concrete erasure correctability excludes non-stabilizer normalizer vectors
--   supported in the erased coordinate region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L238-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L238-L262

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

theorem QEC.Locality.normalizer_inf_coordinateSubspace_le_stabilizer
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery) :
    FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace ⊓
      coordinateSubspace S.selected ≤ P.code.1.generatedVectorSubspace := by sorry
