-- Prove2me | Theorems.Thm_PermanentRollout_affine_sum_range_degree_shift
-- name    : PermanentRollout.affine_sum_range_degree_shift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/31448894-5313-424a-838a-2fc76a5aa3e6
-- title:
--   PermanentRollout.affine_sum_range_degree_shift
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

theorem PermanentRollout.affine_sum_range_degree_shift
    (H : ℕ → ℕ) (d N : ℕ) :
    (∑ m ∈ Finset.range N, if d ≤ m then H (m - d) else 0) =
      ∑ m ∈ Finset.range (N - d), H m := by sorry
