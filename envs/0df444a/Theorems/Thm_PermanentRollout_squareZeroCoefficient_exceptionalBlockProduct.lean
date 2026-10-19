-- Prove2me | Theorems.Thm_PermanentRollout_squareZeroCoefficient_exceptionalBlockProduct
-- name    : PermanentRollout.squareZeroCoefficient_exceptionalBlockProduct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/e4263b4b-6bdc-4a2a-bc26-928c8ec689bb
-- title:
--   PermanentRollout.squareZeroCoefficient_exceptionalBlockProduct
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareZeroCoefficient_exceptionalBlockProduct
    {r : ℕ} {ι : Type*}
    (blocks : ι → Finset (Fin r)) (indices : Finset ι)
    (exceptional : ι) (t d : ℕ)
    (target : Finset (Fin r))
    (hcard : ∀ i ∈ indices, (blocks i).card = t)
    (hdisjoint : Set.PairwiseDisjoint (↑indices) blocks) :
    squareZeroCoefficient r target
      (squareZeroBlockSum r (blocks exceptional) ^ (t - d) *
        ∏ i ∈ indices, squareZeroBlockSum r (blocks i) ^ t) =
      if indices.biUnion blocks ⊆ target ∧
          target \ indices.biUnion blocks ⊆ blocks exceptional ∧
          (target \ indices.biUnion blocks).card = t - d then
        ((t.factorial ^ indices.card : ℕ) : ℂ) *
          (((t - d).factorial : ℕ) : ℂ)
      else 0 := by sorry
