-- Prove2me | Theorems.Thm_ShiQMACenteredGap_approximate_centering_bias_budget
-- name    : ShiQMACenteredGap.approximate_centering_bias_budget
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T09:20:50.512793+00:00
-- url     : https://prove2.me/theorems/09556cec-b264-4a47-88a8-c94f99c5d0b1
-- title:
--   Inverse QMA gap yields a normalization bias budget
-- statement:
--   Under an inverse gap bound and a sufficiently accurate centering coin, the centered acceptance probabilities have bias d=(a-b)/8. This bias is nonnegative, at most one half, and large enough for the logarithmic majority schedule.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-affine-centering.lean#L53-L67

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Theorems.Thm_ShiQMACenteredGap_approximate_centering
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.approximate_centering_bias_budget {a b u : ℝ} (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hab : b ≤ a) (q : Nat)
    (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    let d := (a - b) / 8
    0 ≤ d ∧ d ≤ 1 / 2 ∧ (1 / 6 : ℝ) ≤ (2 * q : Nat) * d ∧
    (∀ t : ℝ, a ≤ t → 1 / 2 + d ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - d) := by
  sorry
