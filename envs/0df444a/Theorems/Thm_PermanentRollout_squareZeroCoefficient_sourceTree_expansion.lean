-- Prove2me | Theorems.Thm_PermanentRollout_squareZeroCoefficient_sourceTree_expansion
-- name    : PermanentRollout.squareZeroCoefficient_sourceTree_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/13c1c085-cae9-4ef3-a00f-53c8f454b203
-- title:
--   PermanentRollout.squareZeroCoefficient_sourceTree_expansion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareZeroCoefficient_sourceTree_expansion
    (b t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ)
    (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d) :
    squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (subtreeLinearFormProduct
          (fun h => squareZeroBlockSum (b * t) (sourceRowBlock b t h))
          t d ζ tree) =
      ∑ h : Fin b,
        subtreeCoefficient
            (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h *
          if omitted ⊆ sourceRowBlock b t h then
            ((t.factorial ^ (b - 1) : ℕ) : ℂ) *
              (((t - d).factorial : ℕ) : ℂ)
          else 0 := by sorry
