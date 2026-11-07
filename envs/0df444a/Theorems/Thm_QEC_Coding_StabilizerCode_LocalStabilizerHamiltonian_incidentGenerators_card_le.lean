-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_incidentGenerators_card_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.incidentGenerators_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:07.402375+00:00
-- url     : https://prove2.me/theorems/c38d5323-691b-40d5-bc12-d2035427ce48
-- title:
--   Local Stabilizer Hamiltonian: incident Generators card le
-- statement:
--   The number of selected terms incident on a qubit obeys the recorded bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L109-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L109-L112

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.incidentGenerators_card_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (i : ι) :
    (H.incidentGenerators i).card ≤ H.participationBound := by sorry
