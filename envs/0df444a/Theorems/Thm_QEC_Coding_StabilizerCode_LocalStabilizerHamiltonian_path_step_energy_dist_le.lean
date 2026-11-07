-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_path_step_energy_dist_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.path_step_energy_dist_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:55:46.159194+00:00
-- url     : https://prove2.me/theorems/67c92085-017d-4421-9ee0-ae1cbc9ccb0e
-- title:
--   Local Stabilizer Hamiltonian: path step energy dist le
-- statement:
--   Every adjacent pair of stored path states obeys the local energy-change bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L390-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L390-L399

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.path_step_energy_dist_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (H.btExcessEnergy (γ.stateAt (n + 1)))
        (H.btExcessEnergy (γ.stateAt n)) ≤
      2 * H.participationBound := by sorry
