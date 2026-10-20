-- Prove2me | Theorems.Thm_PermanentRollout_affine_cumulative_iterate_le_degree_product
-- name    : PermanentRollout.affine_cumulative_iterate_le_degree_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/f8947b6b-bd4e-42d5-9c31-3b8611642323
-- title:
--   PermanentRollout.affine_cumulative_iterate_le_degree_product
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

theorem PermanentRollout.affine_cumulative_iterate_le_degree_product
    (H : ℕ → ℕ → ℕ) (d : ℕ → ℕ) (n : ℕ)
    (hmono : ∀ i, i < n → Monotone (H i))
    (hstep : ∀ i, i < n → ∀ m,
      H (i + 1) m +
        (if d i ≤ m then H i (m - d i) else 0) ≤ H i m)
    (M : ℕ) :
    (affineCumulative^[n]) (H n) M ≤
      (∏ i ∈ Finset.range n, d i) * H 0 M := by sorry
