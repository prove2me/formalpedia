-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_apply_codeword
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_apply_codeword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:00.909081+00:00
-- url     : https://prove2.me/theorems/ba62feaa-6e9f-46a0-b031-5385247c8ece
-- title:
--   Local Stabilizer Hamiltonian: generator Operator apply codeword
-- statement:
--   The selected generator operator fixes every vector in the existing source-valid
--   code. This derives fixedness from generated-group membership rather than adding
--   it as a Hamiltonian field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L156-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L156-L163

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_apply_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.generatorOperator j ψ = ψ := by sorry
