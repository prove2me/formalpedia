-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_operator_apply_error_codeword
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.operator_apply_error_codeword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:53:50.005092+00:00
-- url     : https://prove2.me/theorems/0530afbd-a713-478f-8643-a5f9b0dad5f2
-- title:
--   Local Stabilizer Hamiltonian: operator apply error codeword
-- statement:
--   The full Hamiltonian is the sum of its selected excited/ground branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L225-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L225-L237

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.operator_apply_error_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) :
    H.operator (toQubitOperator E ψ) =
      ∑ j, if j ∈ H.violatedGenerators E then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by sorry
