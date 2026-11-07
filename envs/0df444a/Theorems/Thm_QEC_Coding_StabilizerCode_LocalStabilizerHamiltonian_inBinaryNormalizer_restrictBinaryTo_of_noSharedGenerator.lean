-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_inBinaryNormalizer_restrictBinaryTo_of_noSharedGenerator
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_restrictBinaryTo_of_noSharedGenerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:54.561053+00:00
-- url     : https://prove2.me/theorems/231f57c1-a730-4b4a-945e-5c59c6befc87
-- title:
--   Local Stabilizer Hamiltonian: in Binary Normalizer restrict Binary To of no Shared Generator
-- statement:
--   If no selected generator meets both sides of a disjoint two-region cover, a
--   normalizer Pauli restricts to a normalizer Pauli on each side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L841-L892
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L841-L892

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_restrictBinaryTo_of_noSharedGenerator
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hseparated : H.NoSharedGenerator A B)
    (hsupport : support E ⊆ A ∪ B)
    (hE : H.code.1.InBinaryNormalizer E) :
    H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo A E) ∧
      H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo B E) := by sorry
