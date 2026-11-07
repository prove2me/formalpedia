-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_eq_two_mul_unitDefectEnergy
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_two_mul_unitDefectEnergy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:04.54596+00:00
-- url     : https://prove2.me/theorems/c38f2b49-813f-44e9-acce-5278f21ba3ff
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy eq two mul unit Defect Energy
-- statement:
--   The fixed normalization bridge from one-unit defect energy to BT09 excess
--   energy. A later 4D theorem supplies the geometric loop-length identification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L113-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L113-L117

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_eq_two_mul_unitDefectEnergy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy E = 2 * H.unitDefectEnergy E := by sorry
