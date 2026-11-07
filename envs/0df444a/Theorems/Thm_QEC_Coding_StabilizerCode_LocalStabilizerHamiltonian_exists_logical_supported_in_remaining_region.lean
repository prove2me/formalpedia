-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_logical_supported_in_remaining_region
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_logical_supported_in_remaining_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:51.35121+00:00
-- url     : https://prove2.me/theorems/1e0f3ffe-2060-4715-a40c-56d11c6a0d25
-- title:
--   Local Stabilizer Hamiltonian: exists logical supported in remaining region
-- statement:
--   The abstract alternating-strip step of BT09.  Cleaning every region in the
--   first family leaves a representative supported on the second family; one
--   generator-separated member of that family then carries a nontrivial logical
--   restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1228-L1274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1228-L1274

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_logical_supported_in_remaining_region
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (cleanedRegions remainingRegions : List (Finset ι))
    (hCleanedSeparated :
      cleanedRegions.Pairwise H.NoSharedGenerator)
    (hRemainingDisjoint : remainingRegions.Pairwise Disjoint)
    (hRemainingSeparated :
      remainingRegions.Pairwise H.NoSharedGenerator)
    (hCover :
      regionUnion cleanedRegions ∪ regionUnion remainingRegions =
        (Finset.univ : Finset ι))
    (hNoLocal : ∀ R ∈ cleanedRegions, H.NoLocalLogical R)
    (P : Binary ι)
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ R ∈ remainingRegions, ∃ Q : Binary ι,
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      support Q ⊆ R := by sorry
