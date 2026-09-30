-- Prove2me | Theorems.Thm_RybinAI2026_P01_pair_dot_le_one
-- name    : RybinAI2026.P01.pair_dot_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T21:50:57.291976+00:00
-- url     : https://prove2.me/theorems/2aa87630-aaf8-44ba-a58e-c14ea7b20d8d
-- title:
--   Two-dimensional Cauchy connector for orthogonal directional bounds
-- statement:
--   For four nonnegative real numbers r₁, r₂, s₁, s₂, if each pair has sum of squares at most one, then their dot product r₁s₁+r₂s₂ is at most one. This is the Cauchy-Schwarz connector that combines the two orthogonal directional contraction estimates in the rank-one reduction for RybinAI2026.P01.matrix_integral_inequality.
-- source:
--   Cauchy-Schwarz consequence used in the orthogonal rank-one reduction of RybinAI2026.P01.matrix_integral_inequality (mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733).

import Mathlib

theorem RybinAI2026.P01.pair_dot_le_one {r₁ r₂ s₁ s₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hr : r₁ ^ 2 + r₂ ^ 2 ≤ 1)
    (hs : s₁ ^ 2 + s₂ ^ 2 ≤ 1) :
    r₁ * s₁ + r₂ * s₂ ≤ 1 := by
  sorry
