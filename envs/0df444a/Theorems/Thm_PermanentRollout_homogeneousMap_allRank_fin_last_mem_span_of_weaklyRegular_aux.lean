-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular_aux
-- name    : PermanentRollout.homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/750ebb27-d800-4b97-b6d9-f52e05061673
-- title:
--   PermanentRollout.homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular_aux
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular_aux
    {R : Type*} [CommRing R] {n : ℕ}
    (f : Fin (n + 1) → R)
    (hregular : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f))
    {a : R}
    (ha : f (Fin.last n) * a ∈
      Ideal.span (Set.range fun i : Fin n => f i.castSucc)) :
    a ∈ Ideal.span (Set.range fun i : Fin n => f i.castSucc) := by sorry
