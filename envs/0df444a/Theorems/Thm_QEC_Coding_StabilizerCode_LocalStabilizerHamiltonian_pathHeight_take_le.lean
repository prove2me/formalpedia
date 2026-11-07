-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_take_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_take_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:13.866166+00:00
-- url     : https://prove2.me/theorems/01e3649f-08f7-42c2-aa0b-456cae077607
-- title:
--   Local Stabilizer Hamiltonian: path Height take le
-- statement:
--   Taking a prefix cannot increase the maximum path energy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L170-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L170-L182

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_take_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    H.pathHeight (γ.take n) ≤ H.pathHeight γ := by sorry
