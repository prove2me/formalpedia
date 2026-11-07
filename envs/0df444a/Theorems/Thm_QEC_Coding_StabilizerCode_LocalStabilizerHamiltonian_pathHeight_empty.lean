-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_empty
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:02.556501+00:00
-- url     : https://prove2.me/theorems/d73fc7bc-6068-4c2d-ab0f-9e2b466b5163
-- title:
--   Local Stabilizer Hamiltonian: path Height empty
-- statement:
--   The empty path has zero height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L163-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L163-L167

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_empty
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.pathHeight (PauliErrorPath.empty (ι := ι)) = 0 := by sorry
