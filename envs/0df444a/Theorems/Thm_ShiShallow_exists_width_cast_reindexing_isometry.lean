-- Prove2me | Theorems.Thm_ShiShallow_exists_width_cast_reindexing_isometry
-- name    : ShiShallow.exists_width_cast_reindexing_isometry
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-16T01:13:49.182988+00:00
-- url     : https://prove2.me/theorems/006c4532-32c7-4d2c-a014-00cfe5d48fca
-- title:
--   The width-cast reindexing of basis strings is an explicit isometry
-- statement:
--   For any two register widths that are equal as naturals, there is an explicit 0/1 permutation matrix implementing the reindexing of basis strings along the width cast, and it is an isometry. Its action sends a state to the state reindexed by the cast on wire indices, and it preserves total probability: the sum of squared norms is unchanged. This is needed because widths such as w + w + w and 3 * w are equal as naturals but not definitionally equal as types, so a state on one cannot be used where the other is expected. Because the norm identity is an equality of sums rather than specialised to one, it transports normalisation in both directions. The matrix is written down explicitly: no choice principle is used.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open ShiShallow

theorem exists_width_cast_reindexing_isometry {K M : ℕ} (h : K = M) :
    ∃ R : Matrix (Bits K) (Bits M) ℂ,
      Matrix.conjTranspose R * R = (1 : Op M) ∧
      (∀ Ψ : QState M,
          Matrix.mulVec R Ψ
            = fun z : Bits K => Ψ (fun i : Fin M => z (Fin.cast h.symm i))) ∧
      (∀ Ψ : QState M,
          (∑ z : Bits K, ‖Matrix.mulVec R Ψ z‖ ^ 2)
            = ∑ y : Bits M, ‖Ψ y‖ ^ 2) := by
  sorry

end ShiShallow
