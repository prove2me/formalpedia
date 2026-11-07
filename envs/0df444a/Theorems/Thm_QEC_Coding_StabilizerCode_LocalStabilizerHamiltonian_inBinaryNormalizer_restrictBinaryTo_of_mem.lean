-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_inBinaryNormalizer_restrictBinaryTo_of_mem
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_restrictBinaryTo_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:29.766127+00:00
-- url     : https://prove2.me/theorems/dbd9b162-bf8b-4b97-bb7f-c66525578cc6
-- title:
--   Local Stabilizer Hamiltonian: in Binary Normalizer restrict Binary To of mem
-- statement:
--   A member of a generator-separated covering partition inherits normalizer membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1029-L1070
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1029-L1070

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_restrictBinaryTo_of_mem
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hseparated : regions.Pairwise H.NoSharedGenerator)
    (E : Binary ι) (hsupport : support E ⊆ regionUnion regions)
    (hE : H.code.1.InBinaryNormalizer E)
    (R : Finset ι) (hR : R ∈ regions) :
    H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo R E) := by sorry
