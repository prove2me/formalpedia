-- Prove2me | Theorems.Thm_Real_tendsto_atTop_of_add_le_step
-- name    : Real.tendsto_atTop_of_add_le_step
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:35:20.450441+00:00
-- url     : https://prove2.me/theorems/77b69d6d-3846-441b-a823-94521bc1d027
-- title:
--   A continuous function gaining at least one over each step of fixed length tends to $+\infty$
-- statement:
--   Let $m:\mathbb R\to\mathbb R$ be continuous, $L>0$ and $s_0\in\mathbb R$, with $m(s)+1\le m(s+L)$ for all $s\ge s_0$. Then $m(s)\to+\infty$ as $s\to+\infty$.
--
--   Formalization Note: the conclusion is `Tendsto m atTop atTop`.
-- source:
--   Standard

import Mathlib

namespace Real

open Filter Topology

/-- Let `m : ℝ → ℝ` be continuous and `L > 0`, with `m s + 1 ≤ m (s + L)` for every
`s ≥ s₀`. Then `m s → +∞` as `s → +∞`. -/
theorem tendsto_atTop_of_add_le_step (m : ℝ → ℝ) (hm : Continuous m) (L s₀ : ℝ)
    (hL : 0 < L) (hstep : ∀ s, s₀ ≤ s → m s + 1 ≤ m (s + L)) : Tendsto m atTop atTop := by
  sorry

end Real
