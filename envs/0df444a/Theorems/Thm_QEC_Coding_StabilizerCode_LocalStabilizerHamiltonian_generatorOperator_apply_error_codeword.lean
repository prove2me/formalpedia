-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_apply_error_codeword
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_apply_error_codeword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:17.072106+00:00
-- url     : https://prove2.me/theorems/7614c365-9cc1-4347-9a33-08d8f47b8b01
-- title:
--   Local Stabilizer Hamiltonian: generator Operator apply error codeword
-- statement:
--   On a Pauli-error codeword, one selected generator has eigenvalue `+1` when it
--   commutes with the error and `-1` when it anticommutes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L169-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L169-L199

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_apply_error_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.generatorOperator j (toQubitOperator E ψ) =
      if Commutes E (H.generators j) then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by sorry
