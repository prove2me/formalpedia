-- Prove2me | Theorems.Thm_PermanentRollout_affine_gate_prefix_evaluation_instruction_eq_graph
-- name    : PermanentRollout.affine_gate_prefix_evaluation_instruction_eq_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/ca0106c0-bee8-468e-b354-9edb81e52ca2
-- title:
--   PermanentRollout.affine_gate_prefix_evaluation_instruction_eq_graph
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

theorem PermanentRollout.affine_gate_prefix_evaluation_instruction_eq_graph
    {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (j : Fin q)
    (hprevious : ∀ i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (hgate : gate j = affineGateGraphEvaluation gate (rhs j)) :
    affineGatePrefixEvaluation gate j.val
        (MvPolynomial.X (Sum.inr j) - rhs j) =
      MvPolynomial.X (Sum.inr j) -
        MvPolynomial.rename Sum.inl (gate j) := by sorry
