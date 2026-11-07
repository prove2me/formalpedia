-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_dist_binaryMul_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_dist_binaryMul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:53.518628+00:00
-- url     : https://prove2.me/theorems/31b558b8-8d0d-4998-a190-cbf2ad9b523e
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy dist binary Mul le
-- statement:
--   One allowed local Pauli increment changes energy by a uniformly bounded amount.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L356-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L356-L387

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_dist_binaryMul_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E step : Binary ι) (hstep : weight step ≤ 1) :
    Nat.dist (H.btExcessEnergy (binaryMul E step)) (H.btExcessEnergy E) ≤
      2 * H.participationBound := by sorry
