-- Prove2me | Theorems.Thm_PermanentRollout_sourceTreeMatrix_alpha_eq_factorial
-- name    : PermanentRollout.sourceTreeMatrix_alpha_eq_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/3d546302-06fb-40c8-9e14-a1e6442e91d7
-- title:
--   PermanentRollout.sourceTreeMatrix_alpha_eq_factorial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceTreeMatrix_alpha_eq_factorial
    (b t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ)
    (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d) (h : Fin b)
    (hsubset : omitted ⊆ sourceRowBlock b t h) :
    sourceBlockAlpha (b * t) d
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves)
        omitted =
      subtreeCoefficient
          (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h *
        (((t - d).factorial : ℕ) : ℂ) *
        (((t.factorial : ℕ) : ℂ) ^ (b - 1)) := by sorry
