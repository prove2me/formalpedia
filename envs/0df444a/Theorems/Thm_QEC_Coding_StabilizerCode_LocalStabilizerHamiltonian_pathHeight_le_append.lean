-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_le_append
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_le_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:15.062192+00:00
-- url     : https://prove2.me/theorems/ed9ea98a-9bb5-4fe6-9318-6a1481a164c2
-- title:
--   Local Stabilizer Hamiltonian: path Height le append
-- statement:
--   Concatenating more increments cannot lower the maximum on the left path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L185-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L185-L199

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_le_append
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ δ : PauliErrorPath (ι := ι)) :
    H.pathHeight γ ≤ H.pathHeight (γ.append δ) := by sorry
