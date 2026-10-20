-- Prove2me | Theorems.Thm_PermanentRollout_finite_of_totalDegree_power_reductions
-- name    : PermanentRollout.finite_of_totalDegree_power_reductions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/491f5616-a7cb-4ae6-8eba-7461d2963050
-- title:
--   PermanentRollout.finite_of_totalDegree_power_reductions
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.finite_of_totalDegree_power_reductions
    {ι B A : Type*} [Fintype ι] [CommRing B] [CommRing A] [Algebra B A]
    (x : ι → A) (q : ℕ) (_hq : 0 < q)
    (remainder : ι → MvPolynomial ι B)
    (hdegree : ∀ i, (remainder i).totalDegree < q)
    (hrel : ∀ i, x i ^ q = MvPolynomial.aeval x (remainder i))
    (hgen : Algebra.adjoin B (Set.range x) = ⊤) :
    Module.Finite B A := by sorry
