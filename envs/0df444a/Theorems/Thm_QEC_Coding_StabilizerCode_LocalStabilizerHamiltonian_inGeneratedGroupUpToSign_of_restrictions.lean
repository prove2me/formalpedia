-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_inGeneratedGroupUpToSign_of_restrictions
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inGeneratedGroupUpToSign_of_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:20.676689+00:00
-- url     : https://prove2.me/theorems/a64bec2d-2aca-4c18-a14f-f144c78a2e8f
-- title:
--   Local Stabilizer Hamiltonian: in Generated Group Up To Sign of restrictions
-- statement:
--   If all restrictions of a Pauli to a disjoint supporting partition are generated
--   up to sign, then the original Pauli is generated up to sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L996-L1026
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L996-L1026

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inGeneratedGroupUpToSign_of_restrictions
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise Disjoint)
    (E : Binary ι) (hsupport : support E ⊆ regionUnion regions)
    (hgenerated :
      ∀ R ∈ regions,
        H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E)) :
    H.code.1.InGeneratedGroupUpToSign E := by sorry
