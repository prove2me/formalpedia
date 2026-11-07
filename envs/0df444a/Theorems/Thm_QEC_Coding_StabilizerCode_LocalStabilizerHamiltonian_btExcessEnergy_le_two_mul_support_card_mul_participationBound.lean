-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_le_two_mul_support_card_mul_participationBound
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_le_two_mul_support_card_mul_participationBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:38:21.21666+00:00
-- url     : https://prove2.me/theorems/1340af82-474c-4e87-9431-59502e6a9b0c
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy le two mul support card mul participation Bound
-- statement:
--   A finite-support error has energy bounded by support size times participation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L87-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L87-L103

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_le_two_mul_support_card_mul_participationBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy E ≤
      2 * (support E).card * H.participationBound := by sorry
