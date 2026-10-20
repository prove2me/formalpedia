-- Prove2me | Theorems.Thm_PermanentRollout_sourceRowBlock_weighted_minor_sum
-- name    : PermanentRollout.sourceRowBlock_weighted_minor_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/f5929928-8cb0-422e-b166-cd7e33803edd
-- title:
--   PermanentRollout.sourceRowBlock_weighted_minor_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceRowBlock_weighted_minor_sum
    {R : Type*} [CommSemiring R]
    (b t s d : ℕ) (X : Matrix (Fin (b * t)) (Fin s) R)
    (weight : Fin b → R) :
    (∑ omitted ∈ (Finset.univ : Finset (Fin (b * t))).powersetCard d,
      (∑ h : Fin b,
        if omitted ⊆ sourceRowBlock b t h then weight h else 0) *
        ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockMinor (b * t) s X omitted columns) =
      ∑ h : Fin b, weight h * sourceRowBlockMinorSum b t s d X h := by sorry
