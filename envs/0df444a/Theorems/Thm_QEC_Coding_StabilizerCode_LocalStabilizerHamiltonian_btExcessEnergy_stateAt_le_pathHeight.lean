-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_stateAt_le_pathHeight
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_stateAt_le_pathHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:42.926221+00:00
-- url     : https://prove2.me/theorems/62921424-d627-4a77-8c11-3e10886054c4
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy state At le path Height
-- statement:
--   Every state indexed along the path has energy at most the path height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L143-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L143-L151

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_stateAt_le_pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n ≤ γ.increments.length) :
    H.btExcessEnergy (γ.stateAt n) ≤ H.pathHeight γ := by sorry
