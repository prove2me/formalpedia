-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryMul_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryMul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:05.162387+00:00
-- url     : https://prove2.me/theorems/07905122-2bba-4c87-9777-47517ef550af
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy binary Mul le
-- statement:
--   BT09 excess energy is subadditive under Pauli multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L251-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L251-L257

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryMul_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) :
    H.btExcessEnergy (binaryMul E F) ≤
      H.btExcessEnergy E + H.btExcessEnergy F := by sorry
