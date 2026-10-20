-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineInputCombination_not_mem_gate_vars
-- name    : PermanentRollout.freeAffineInputCombination_not_mem_gate_vars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/574eb28e-8d7c-4820-886d-6e75c30a0192
-- title:
--   PermanentRollout.freeAffineInputCombination_not_mem_gate_vars
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.freeAffineInputCombination_not_mem_gate_vars
    {k n : ℕ} (coefficients : Fin k →₀ ℂ) (i : Fin n) :
    Sum.inr i ∉
      (Finsupp.linearCombination ℂ
        (fun a : Fin k => MvPolynomial.X (Sum.inl a))
        coefficients : MvPolynomial (Fin k ⊕ Fin n) ℂ).vars := by sorry
