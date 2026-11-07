-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_card_incidentGeneratorUnion_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.card_incidentGeneratorUnion_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:29:25.802194+00:00
-- url     : https://prove2.me/theorems/6492328e-505b-456d-a2da-0c52bcc30da0
-- title:
--   Local Stabilizer Hamiltonian: card incident Generator Union le
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the card incident Generator Union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L30-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean#L30-L38

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.card_incidentGeneratorUnion_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    (H.incidentGeneratorUnion R).card ≤
      R.card * H.participationBound := by sorry
