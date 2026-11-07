-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_incidentGeneratorUnion_of_mem_generatorSupport
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_incidentGeneratorUnion_of_mem_generatorSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:29:21.276956+00:00
-- url     : https://prove2.me/theorems/bdf64559-da8e-420b-90a2-0bc981209bf8
-- title:
--   Local Stabilizer Hamiltonian: mem incident Generator Union of mem generator Support
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the mem incident Generator Union of mem generator Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L40-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L40-L48

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_incidentGeneratorUnion_of_mem_generatorSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (i : ι) (j : κ)
    (hiR : i ∈ R) (hij : i ∈ support (H.generators j)) :
    j ∈ H.incidentGeneratorUnion R := by sorry
