-- Prove2me | Theorems.Thm_PermanentRollout_affine_total_degree_cumulative_iterate_regular
-- name    : PermanentRollout.affine_total_degree_cumulative_iterate_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/7e509813-9a96-44ba-8e22-38e35b124e8a
-- title:
--   PermanentRollout.affine_total_degree_cumulative_iterate_regular
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

theorem PermanentRollout.affine_total_degree_cumulative_iterate_regular
    {ι : Type*} [Fintype ι]
    (I : ℕ → Ideal (MvPolynomial ι ℂ))
    (g : ℕ → MvPolynomial ι ℂ)
    (n : ℕ)
    (hzero : I 0 = ⊥)
    (hnext : ∀ i, i < n →
      I (i + 1) = I i ⊔ Ideal.span ({g i} : Set (MvPolynomial ι ℂ)))
    (hregular : ∀ i, i < n →
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I i) (g i))
    (M : ℕ) :
    (affineCumulative^[n]) (affineTotalDegreeHilbert (I n)) M ≤
      (∏ i ∈ Finset.range n, (g i).totalDegree) *
        (M + Fintype.card ι).choose (Fintype.card ι) := by sorry
