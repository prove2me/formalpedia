-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlockMatchingExpansion_eq_sum_glued_fibres
-- name    : PermanentRollout.sourceBlockMatchingExpansion_eq_sum_glued_fibres
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/126d7949-04c1-4799-bcb1-7922d22c7050
-- title:
--   PermanentRollout.sourceBlockMatchingExpansion_eq_sum_glued_fibres
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem PermanentRollout.sourceBlockMatchingExpansion_eq_sum_glued_fibres
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R) :
    sourceBlockMatchingExpansion r s d X U =
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powersetCard d,
        ∑ J ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockGluedFibre r s d X U I J := by sorry
