-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_logicalCoset_binaryMul_generated_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalCoset_binaryMul_generated_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:55:56.335061+00:00
-- url     : https://prove2.me/theorems/9a9feb69-d726-41c7-b313-b9c158a43dce
-- title:
--   Local Stabilizer Hamiltonian: logical Coset binary Mul generated iff
-- statement:
--   Multiplying by a generated stabilizer preserves both the logical normalizer
--   sector and the nontrivial generated-group coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L405-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L405-L428

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalCoset_binaryMul_generated_iff
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    (H.code.1.InBinaryNormalizer (binaryMul E S) ∧
        ¬ H.code.1.InGeneratedGroupUpToSign (binaryMul E S)) ↔
      (H.code.1.InBinaryNormalizer E ∧
        ¬ H.code.1.InGeneratedGroupUpToSign E) := by sorry
