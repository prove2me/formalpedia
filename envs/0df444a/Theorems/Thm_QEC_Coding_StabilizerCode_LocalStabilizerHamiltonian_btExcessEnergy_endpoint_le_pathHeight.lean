-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_endpoint_le_pathHeight
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_endpoint_le_pathHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:05.468596+00:00
-- url     : https://prove2.me/theorems/d40ba99a-b4ca-4b67-bacc-25241d7e260b
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy endpoint le path Height
-- statement:
--   The endpoint energy is bounded by the path height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L154-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L154-L159

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_endpoint_le_pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) :
    H.btExcessEnergy γ.endpoint ≤ H.pathHeight γ := by sorry
