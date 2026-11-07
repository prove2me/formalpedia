-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_commute
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:46.364214+00:00
-- url     : https://prove2.me/theorems/6158ec25-2a8d-49b3-826a-12ee47972955
-- title:
--   Local Stabilizer Hamiltonian: term commute
-- statement:
--   Unit-coefficient Hamiltonian terms commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L152-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L152-L155

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_commute
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commute (H.term j) (H.term k) := by sorry
