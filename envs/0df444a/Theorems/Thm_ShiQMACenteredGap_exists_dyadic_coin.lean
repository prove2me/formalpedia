-- Prove2me | Theorems.Thm_ShiQMACenteredGap_exists_dyadic_coin
-- name    : ShiQMACenteredGap.exists_dyadic_coin
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T09:32:51.538809+00:00
-- url     : https://prove2.me/theorems/c10a7e89-4cbc-48b2-bbcb-0067548ab991
-- title:
--   Approximate a probability by a finite fair-bit coin
-- statement:
--   For every probability u in [0,1] and natural bit count k, some integer j between 0 and 2^k gives a dyadic probability j/2^k within 2^-k of u.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-dyadic-centering.lean#L8-L25

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.exists_dyadic_coin {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (k : Nat) :
    ∃ j : Nat, j ≤ 2 ^ k ∧
      |(j : ℝ) / (2 : ℝ) ^ k - u| < 1 / (2 : ℝ) ^ k := by
  sorry
