-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_logicalEnergyBarrier_le_pathHeight
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalEnergyBarrier_le_pathHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:31.248532+00:00
-- url     : https://prove2.me/theorems/7a93c676-62d3-4300-9e77-06cfd2df0f87
-- title:
--   Local Stabilizer Hamiltonian: logical Energy Barrier le path Height
-- statement:
--   Any concrete logical path gives an upper bound on the logical barrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L202-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L202-L206

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalEnergyBarrier_le_pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (hγ : H.HasLogicalEndpoint γ) :
    H.logicalEnergyBarrier ≤ H.pathHeight γ := by sorry
