-- Prove2me | Theorems.Thm_QEC_QLDPC_hasUniformLDPC_iff_components
-- name    : QEC.QLDPC.hasUniformLDPC_iff_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:35.464139+00:00
-- url     : https://prove2.me/theorems/3ac01b5a-0187-4cc2-9e9c-a6f876d6e145
-- title:
--   QLDPC: has Uniform LDPC iff components
-- statement:
--   Uniform incidence locality is equivalent to one common bound on both
--   observable row weights and variable degrees.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean#L46-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean#L46-L53

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.hasUniformLDPC_iff_components (F : QuantumCodeFamily A ι κ) :
    HasUniformLDPC F ↔
      ∃ B : Nat, ∀ a, F.maxCheckWeight a ≤ B ∧ F.maxVariableDegree a ≤ B := by sorry
