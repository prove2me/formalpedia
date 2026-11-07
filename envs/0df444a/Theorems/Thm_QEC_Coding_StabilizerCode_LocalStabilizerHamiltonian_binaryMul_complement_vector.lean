-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_binaryMul_complement_vector
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.binaryMul_complement_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:05.034543+00:00
-- url     : https://prove2.me/theorems/a53960f9-44b3-42a7-98dd-bef8683c6a4a
-- title:
--   Local Stabilizer Hamiltonian: binary Mul complement vector
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the binary Mul complement vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L653-L673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L653-L673

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.binaryMul_complement_vector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q E F : Binary ι) (hdecomp : Q.vector = E.vector + F.vector) :
    (binaryMul Q F).vector = E.vector := by sorry
