-- Prove2me | Theorems.Thm_PermanentRollout_affine_finrank_le_degree_product_of_regular_prefix
-- name    : PermanentRollout.affine_finrank_le_degree_product_of_regular_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/18a5b5dd-9379-42d7-8116-39dbaaab8ebc
-- title:
--   PermanentRollout.affine_finrank_le_degree_product_of_regular_prefix
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

theorem PermanentRollout.affine_finrank_le_degree_product_of_regular_prefix
    {ι : Type*} [Fintype ι]
    (I : ℕ → Ideal (MvPolynomial ι ℂ))
    (g : ℕ → MvPolynomial ι ℂ)
    (hzero : I 0 = ⊥)
    (hnext : ∀ i, i < Fintype.card ι →
      I (i + 1) = I i ⊔ Ideal.span ({g i} : Set (MvPolynomial ι ℂ)))
    (hregular : ∀ i, i < Fintype.card ι →
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I i) (g i))
    [Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I (Fintype.card ι))] :
    Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I (Fintype.card ι)) ≤
      ∏ i ∈ Finset.range (Fintype.card ι), (g i).totalDegree := by sorry
