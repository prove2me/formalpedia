-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_eq_of_vector_eq
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_eq_of_vector_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:08.329781+00:00
-- url     : https://prove2.me/theorems/a8ad8578-d35f-42b0-ac61-b8c6fb45d471
-- title:
--   Local Stabilizer Hamiltonian: violated Generators eq of vector eq
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the violated Generators eq of vector eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L637-L643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L637-L643

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_eq_of_vector_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) (hvector : E.vector = F.vector) :
    H.violatedGenerators E = H.violatedGenerators F := by sorry
