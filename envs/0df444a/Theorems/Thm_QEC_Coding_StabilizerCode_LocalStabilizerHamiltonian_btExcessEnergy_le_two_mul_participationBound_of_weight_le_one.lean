-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_le_two_mul_participationBound_of_weight_le_one
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_le_two_mul_participationBound_of_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:29:07.266223+00:00
-- url     : https://prove2.me/theorems/a7659937-6e16-465b-bb59-0719e7f9def7
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy le two mul participation Bound of weight le one
-- statement:
--   A one-qubit step has BT09 excess energy at most twice the participation bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L348-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L348-L353

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_le_two_mul_participationBound_of_weight_le_one
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (step : Binary ι) (hstep : weight step ≤ 1) :
    H.btExcessEnergy step ≤ 2 * H.participationBound := by sorry
