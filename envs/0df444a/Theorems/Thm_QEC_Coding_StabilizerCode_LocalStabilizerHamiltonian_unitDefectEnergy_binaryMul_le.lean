-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_binaryMul_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_binaryMul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:17.29259+00:00
-- url     : https://prove2.me/theorems/68261d99-bb3a-44a5-a01f-ba93cd750a43
-- title:
--   Local Stabilizer Hamiltonian: unit Defect Energy binary Mul le
-- statement:
--   Selected unit-defect energy is subadditive under Pauli multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L237-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L237-L248

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_binaryMul_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) :
    H.unitDefectEnergy (binaryMul E F) ≤
      H.unitDefectEnergy E + H.unitDefectEnergy F := by sorry
