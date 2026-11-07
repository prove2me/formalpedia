-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_nontrivial_logical_restriction
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_nontrivial_logical_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:33:21.228+00:00
-- url     : https://prove2.me/theorems/406d9a15-114c-444f-9181-daa565df17cf
-- title:
--   Local Stabilizer Hamiltonian: exists nontrivial logical restriction
-- statement:
--   A nontrivial logical Pauli supported on a disjoint, generator-separated finite
--   partition has a nontrivial logical restriction on at least one member.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1076-L1104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1076-L1104

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_nontrivial_logical_restriction
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hdisjoint : regions.Pairwise Disjoint)
    (hseparated : regions.Pairwise H.NoSharedGenerator)
    (E : Binary ι)
    (hNormalizer : H.code.1.InBinaryNormalizer E)
    (hNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign E)
    (hsupport : support E ⊆ regionUnion regions) :
    ∃ R ∈ regions,
      H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo R E) ∧
      ¬ H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E) ∧
      support (Locality.restrictBinaryTo R E) ⊆ R := by sorry
