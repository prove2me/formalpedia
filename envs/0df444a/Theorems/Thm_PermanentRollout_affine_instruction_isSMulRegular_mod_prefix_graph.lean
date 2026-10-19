-- Prove2me | Theorems.Thm_PermanentRollout_affine_instruction_isSMulRegular_mod_prefix_graph
-- name    : PermanentRollout.affine_instruction_isSMulRegular_mod_prefix_graph
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/b4d60388-9394-43c0-b8e7-d7db58109a86
-- title:
--   PermanentRollout.affine_instruction_isSMulRegular_mod_prefix_graph
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

theorem PermanentRollout.affine_instruction_isSMulRegular_mod_prefix_graph
    {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (j : Fin q)
    (hprevious : ∀ i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (hgate : gate j = affineGateGraphEvaluation gate (rhs j)) :
    IsSMulRegular
      (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
        affineGatePrefixGraphIdeal gate j.val)
      (MvPolynomial.X (Sum.inr j) - rhs j) := by sorry
