-- Prove2me | Theorems.Thm_PermanentRollout_affine_finrank_le_degree_product_of_weaklyRegular
-- name    : PermanentRollout.affine_finrank_le_degree_product_of_weaklyRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/3f356587-d5c7-4184-a960-a2751628f025
-- title:
--   PermanentRollout.affine_finrank_le_degree_product_of_weaklyRegular
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

theorem PermanentRollout.affine_finrank_le_degree_product_of_weaklyRegular
    {ι : Type*} [Fintype ι]
    (f : Fin (Fintype.card ι) → MvPolynomial ι ℂ)
    (hweak : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial ι ℂ) (List.ofFn f))
    (hfinite :
      (MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range f))).Finite) :
    Module.finrank ℂ
        (MvPolynomial ι ℂ ⧸ Ideal.span (Set.range f)) ≤
      ∏ i, (f i).totalDegree := by sorry
