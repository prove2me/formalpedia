-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_eq_syndromeWeight
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_eq_syndromeWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:25:57.608518+00:00
-- url     : https://prove2.me/theorems/493cc1ba-cf96-423c-9f6f-164ffed885c6
-- title:
--   Local Stabilizer Hamiltonian: unit Defect Energy eq syndrome Weight
-- statement:
--   Unit-defect energy is exactly the selected syndrome weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L96-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L96-L100

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_eq_syndromeWeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.unitDefectEnergy E = H.syndromeWeight E := by sorry
