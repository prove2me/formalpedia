-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_cleanedOutside_regionUnion
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_cleanedOutside_regionUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:28.817813+00:00
-- url     : https://prove2.me/theorems/c45b1cd6-f14c-4568-83be-02ddccd3a924
-- title:
--   Local Stabilizer Hamiltonian: exists cleaned Outside region Union
-- statement:
--   Repeated BT09 cleaning for a pairwise generator-separated list of regions.
--   The returned correction is an actual member of the existing generated group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1120-L1188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1120-L1188

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_cleanedOutside_regionUnion
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise H.NoSharedGenerator)
    (hNoLocal : ∀ R ∈ regions, H.NoLocalLogical R)
    (P : Binary ι) (hP : H.code.1.InBinaryNormalizer P) :
    ∃ S : Binary ι,
      S ∈ H.code.1.generatedGroup ∧
      H.code.1.InBinaryNormalizer (binaryMul P S) ∧
      support (binaryMul P S) ⊆ (regionUnion regions)ᶜ := by sorry
