-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_vector_mem_coordinateSubspace_of_support_subset
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.vector_mem_coordinateSubspace_of_support_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:29.898127+00:00
-- url     : https://prove2.me/theorems/5b658931-9d70-4dd4-99a0-2c70cf26003e
-- title:
--   Local Stabilizer Hamiltonian: vector mem coordinate Subspace of support subset
-- statement:
--   A Pauli supported in a region has its vector in that coordinate subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean#L148-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean#L148-L176

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.vector_mem_coordinateSubspace_of_support_subset
    (R : Finset ι) (E : Binary ι) (hE : support E ⊆ R) :
    E.vector ∈ Locality.coordinateSubspace R := by sorry
