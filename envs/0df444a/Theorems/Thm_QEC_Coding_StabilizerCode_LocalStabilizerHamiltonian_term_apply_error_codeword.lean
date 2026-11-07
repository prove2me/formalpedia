-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_apply_error_codeword
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_apply_error_codeword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:25.610399+00:00
-- url     : https://prove2.me/theorems/2a670c76-a285-47b1-ab8f-9e179e8cba1b
-- title:
--   Local Stabilizer Hamiltonian: term apply error codeword
-- statement:
--   For the unit Hamiltonian term `-S_j`, a violated term contributes the excited
--   `+1` branch and an unviolated term contributes the ground `-1` branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L205-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L205-L222

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_apply_error_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.term j (toQubitOperator E ψ) =
      if j ∈ H.violatedGenerators E then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by sorry
