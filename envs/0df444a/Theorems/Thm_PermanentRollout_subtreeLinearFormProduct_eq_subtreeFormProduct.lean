-- Prove2me | Theorems.Thm_PermanentRollout_subtreeLinearFormProduct_eq_subtreeFormProduct
-- name    : PermanentRollout.subtreeLinearFormProduct_eq_subtreeFormProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/b9051065-c83d-43d1-a0c6-0017a6be9bee
-- title:
--   PermanentRollout.subtreeLinearFormProduct_eq_subtreeFormProduct
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtreeLinearFormProduct_eq_subtreeFormProduct
    {R ι : Type*} [CommRing R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (hd : 0 < d) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (tree : BlockTree ι) :
    subtreeLinearFormProduct y t d ζ tree =
      subtreeFormProduct y t d
        (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree := by sorry
