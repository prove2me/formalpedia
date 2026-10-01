-- Prove2me | Theorems.Thm_ShiQMACenteredGap_exists_dyadic_centering
-- name    : ShiQMACenteredGap.exists_dyadic_centering
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T09:42:43.945298+00:00
-- url     : https://prove2.me/theorems/b60e017f-e2bb-4fca-a4c2-6fc56196eeee
-- title:
--   Dyadic coin precision suffices for QMA threshold centering
-- statement:
--   For completeness and soundness thresholds in [0,1] separated by inverse gap q, a coin with coinBits(q) fair bits approximates the ideal centering probability within one quarter of the gap.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-dyadic-centering.lean#L30-L45

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Theorems.Thm_ShiQMACenteredGap_exists_dyadic_coin
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.exists_dyadic_centering {a b : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hab : b ≤ a) (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b)) :
    ∃ j : Nat, j ≤ 2 ^ coinBits q ∧
      |(j : ℝ) / (2 : ℝ) ^ coinBits q - centeringCoin a b| ≤ (a - b) / 4 := by
  sorry
