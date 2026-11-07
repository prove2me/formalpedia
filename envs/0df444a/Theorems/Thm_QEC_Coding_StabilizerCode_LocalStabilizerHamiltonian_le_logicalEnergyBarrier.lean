-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_le_logicalEnergyBarrier
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.le_logicalEnergyBarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:55:27.49746+00:00
-- url     : https://prove2.me/theorems/90ac9785-a882-4785-93b1-796d5a517e12
-- title:
--   Local Stabilizer Hamiltonian: le logical Energy Barrier
-- statement:
--   A uniform lower bound on all logical paths bounds the logical barrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L209-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L209-L220

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.le_logicalEnergyBarrier
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (bound : Nat)
    (hexists : ∃ γ : PauliErrorPath (ι := ι), H.HasLogicalEndpoint γ)
    (hlower : ∀ γ : PauliErrorPath (ι := ι),
      H.HasLogicalEndpoint γ → bound ≤ H.pathHeight γ) :
    bound ≤ H.logicalEnergyBarrier := by sorry
