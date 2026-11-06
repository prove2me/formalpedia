-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_fixed_generatedStabilizer_iff_fixed_generators
-- name    : QEC.Coding.PauliSymplectic.fixed_generatedStabilizer_iff_fixed_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:40:21.173053+00:00
-- url     : https://prove2.me/theorems/04aa11b0-d0c5-4119-a3aa-40367ea52a59
-- title:
--   Pauli Symplectic: fixed generated Stabilizer iff fixed generators
-- statement:
--   Testing fixedness on a stabilizer closure is equivalent to testing its generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L56-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L56-L65

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

theorem QEC.Coding.PauliSymplectic.fixed_generatedStabilizer_iff_fixed_generators
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι) :
    (∀ P, GeneratedStabilizer generators P → toQubitOperator P ψ = ψ) ↔
      ∀ j, toQubitOperator (generators j) ψ = ψ := by sorry
