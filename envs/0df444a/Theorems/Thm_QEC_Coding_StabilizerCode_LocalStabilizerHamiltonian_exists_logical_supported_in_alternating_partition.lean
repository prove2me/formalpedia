-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_logical_supported_in_alternating_partition
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_logical_supported_in_alternating_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:34:32.315854+00:00
-- url     : https://prove2.me/theorems/1c7c7e5b-325f-45ce-b365-e6bdd3b55694
-- title:
--   Local Stabilizer Hamiltonian: exists logical supported in alternating partition
-- statement:
--   Alternating-strip cleaning without a correctability premise: either a region
--   in the first parity already carries a nontrivial logical, or all of them can
--   be cleaned and a region in the second parity carries one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1281-L1313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1281-L1313

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_logical_supported_in_alternating_partition
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (firstRegions secondRegions : List (Finset ι))
    (hFirstSeparated : firstRegions.Pairwise H.NoSharedGenerator)
    (hSecondDisjoint : secondRegions.Pairwise Disjoint)
    (hSecondSeparated : secondRegions.Pairwise H.NoSharedGenerator)
    (hCover :
      regionUnion firstRegions ∪ regionUnion secondRegions =
        (Finset.univ : Finset ι))
    (P : Binary ι)
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ R ∈ firstRegions ++ secondRegions, ∃ Q : Binary ι,
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      support Q ⊆ R := by sorry
