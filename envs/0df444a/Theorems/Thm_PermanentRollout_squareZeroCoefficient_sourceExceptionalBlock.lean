-- Prove2me | Theorems.Thm_PermanentRollout_squareZeroCoefficient_sourceExceptionalBlock
-- name    : PermanentRollout.squareZeroCoefficient_sourceExceptionalBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/1b2d059e-80ad-4e8e-9c02-c2ead24d8751
-- title:
--   PermanentRollout.squareZeroCoefficient_sourceExceptionalBlock
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareZeroCoefficient_sourceExceptionalBlock
    (b t d : ℕ) (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d) (h : Fin b) :
    squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (squareZeroBlockSum (b * t) (sourceRowBlock b t h) ^ (t - d) *
          ∏ j ∈ (Finset.univ : Finset (Fin b)).erase h,
            squareZeroBlockSum (b * t) (sourceRowBlock b t j) ^ t) =
      if omitted ⊆ sourceRowBlock b t h then
        ((t.factorial ^ (b - 1) : ℕ) : ℂ) *
          (((t - d).factorial : ℕ) : ℂ)
      else 0 := by sorry
