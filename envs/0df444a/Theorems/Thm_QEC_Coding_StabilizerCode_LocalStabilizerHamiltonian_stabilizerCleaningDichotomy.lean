-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_stabilizerCleaningDichotomy
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.stabilizerCleaningDichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:29:32.166816+00:00
-- url     : https://prove2.me/theorems/e45f1fa6-1fb4-4383-9a21-ebd02a0991af
-- title:
--   Local Stabilizer Hamiltonian: stabilizer Cleaning Dichotomy
-- statement:
--   BT09 Cleaning Lemma: either the region supports a nontrivial logical Pauli, or
--   every normalizer representative can be cleaned from the region using only
--   selected generators that meet it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean#L183-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean#L183-L332

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.stabilizerCleaningDichotomy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    (∃ P : Binary ι,
      H.code.1.InBinaryNormalizer P ∧
      ¬ H.code.1.InGeneratedGroupUpToSign P ∧
      support P ⊆ R) ∨
    (∀ P : Binary ι, H.code.1.InBinaryNormalizer P →
      ∃ S : Binary ι,
        H.GeneratedByMeeting R S ∧
        S ∈ H.code.1.generatedGroup ∧
        H.code.1.InBinaryNormalizer (binaryMul P S) ∧
        support (binaryMul P S) ⊆ Rᶜ) := by sorry
