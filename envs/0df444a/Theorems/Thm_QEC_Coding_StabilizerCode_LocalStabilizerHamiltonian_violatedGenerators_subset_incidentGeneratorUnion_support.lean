-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_subset_incidentGeneratorUnion_support
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_subset_incidentGeneratorUnion_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:29:23.006051+00:00
-- url     : https://prove2.me/theorems/ff9694f0-f434-4543-8ebb-e2f825db554d
-- title:
--   Local Stabilizer Hamiltonian: violated Generators subset incident Generator Union support
-- statement:
--   Every violated selected generator is incident on the error support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L67-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L67-L84

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_subset_incidentGeneratorUnion_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators E ⊆ H.incidentGeneratorUnion (support E) := by sorry
