-- Prove2me | Theorems.Thm_PermanentRollout_affine_triangular_instruction_prefix_ideal_ofList
-- name    : PermanentRollout.affine_triangular_instruction_prefix_ideal_ofList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/f2dbd6c9-fd24-4f95-a87f-91f43eed91d6
-- title:
--   PermanentRollout.affine_triangular_instruction_prefix_ideal_ofList
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

theorem PermanentRollout.affine_triangular_instruction_prefix_ideal_ofList
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ) (n : ℕ) :
    Ideal.ofList
        ((List.ofFn fun j : Fin q =>
          MvPolynomial.X (Sum.inr j) - rhs j).take n) =
      affineTriangularInstructionPrefixIdeal rhs n := by sorry
