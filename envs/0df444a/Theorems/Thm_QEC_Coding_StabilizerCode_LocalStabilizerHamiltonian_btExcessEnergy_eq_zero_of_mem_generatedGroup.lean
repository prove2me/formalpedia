-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_eq_zero_of_mem_generatedGroup
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_zero_of_mem_generatedGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:57.489914+00:00
-- url     : https://prove2.me/theorems/9e683a5c-d6de-45ca-aa74-cf16d06c4e02
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy eq zero of mem generated Group
-- statement:
--   Every generated stabilizer has zero selected-generator excess energy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L278-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L278-L288

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_zero_of_mem_generatedGroup
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    H.btExcessEnergy S = 0 := by sorry
