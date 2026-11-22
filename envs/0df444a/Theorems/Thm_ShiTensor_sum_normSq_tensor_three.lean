-- Prove2me | Theorems.Thm_ShiTensor_sum_normSq_tensor_three
-- name    : ShiTensor.sum_normSq_tensor_three
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T07:28:17.416214+00:00
-- url     : https://prove2.me/theorems/7ae3395e-3b64-4042-9b09-54c7d7bca789
-- title:
--   A threefold tensor of normalised states is normalised
-- statement:
--   The total probability of a threefold tensor product of three normalised states is one. The two-block factorisation applies twice, at the outer split and then at the inner one, and the three normalisations multiply to one.
--
--   The wire count is associated to the left, matching the nesting of the iterated tensor, so no reindexing is involved. This is what allows a product witness formed from three copies of a single normalised witness to be used where the class definition demands a normalised witness.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem sum_normSq_tensor_three {m p q : ℕ} (ψ : QState m) (φ : QState p) (χ : QState q)
    (hψ : ∑ a : Bits m, ‖ψ a‖ ^ 2 = 1)
    (hφ : ∑ b : Bits p, ‖φ b‖ ^ 2 = 1)
    (hχ : ∑ c : Bits q, ‖χ c‖ ^ 2 = 1) :
    ∑ y : Bits (m + p + q), ‖tensor (tensor ψ φ) χ y‖ ^ 2 = 1 := by
  sorry

end ShiTensor
