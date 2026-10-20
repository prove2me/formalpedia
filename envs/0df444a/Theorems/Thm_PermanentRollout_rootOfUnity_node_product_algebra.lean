-- Prove2me | Theorems.Thm_PermanentRollout_rootOfUnity_node_product_algebra
-- name    : PermanentRollout.rootOfUnity_node_product_algebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/e074a749-64f1-47fc-8358-8592ad573e65
-- title:
--   PermanentRollout.rootOfUnity_node_product_algebra
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.rootOfUnity_node_product_algebra
    {R : Type*} [CommRing R] [Algebra ℂ R]
    {d : ℕ} (hd : 0 < d) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (x y : R) :
    (∏ j ∈ Finset.range d,
      (x + algebraMap ℂ R (2 * ζ ^ j) * y)) =
      x ^ d - (algebraMap ℂ R (-2) * y) ^ d := by sorry
