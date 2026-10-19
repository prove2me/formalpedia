-- Prove2me | Theorems.Thm_PermanentRollout_affine_total_degree_hilbert_regular_step
-- name    : PermanentRollout.affine_total_degree_hilbert_regular_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/4df138a8-ea77-47fc-991c-acdc5f0bce4e
-- title:
--   PermanentRollout.affine_total_degree_hilbert_regular_step
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

theorem PermanentRollout.affine_total_degree_hilbert_regular_step
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ)) (g : MvPolynomial ι ℂ)
    (hregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) g)
    (m : ℕ) :
    affineTotalDegreeHilbert
        (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ))) m +
      (if g.totalDegree ≤ m then
        affineTotalDegreeHilbert I (m - g.totalDegree) else 0) ≤
          affineTotalDegreeHilbert I m := by sorry
