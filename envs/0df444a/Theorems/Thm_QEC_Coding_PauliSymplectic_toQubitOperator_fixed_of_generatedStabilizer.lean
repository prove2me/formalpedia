-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_fixed_of_generatedStabilizer
-- name    : QEC.Coding.PauliSymplectic.toQubitOperator_fixed_of_generatedStabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:19.317226+00:00
-- url     : https://prove2.me/theorems/dff2c69b-8c56-4d19-9f5d-5525a285541a
-- title:
--   Pauli Symplectic: to Qubit Operator fixed of generated Stabilizer
-- statement:
--   Fixedness under generators extends to their full product-and-adjoint closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L36-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L36-L53

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.toQubitOperator_fixed_of_generatedStabilizer
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hgenerators : ∀ j, toQubitOperator (generators j) ψ = ψ)
    {P : Binary ι} (hP : GeneratedStabilizer generators P) :
    toQubitOperator P ψ = ψ := by sorry
