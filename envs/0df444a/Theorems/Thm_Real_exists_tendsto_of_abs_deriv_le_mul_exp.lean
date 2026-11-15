-- Prove2me | Theorems.Thm_Real_exists_tendsto_of_abs_deriv_le_mul_exp
-- name    : Real.exists_tendsto_of_abs_deriv_le_mul_exp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:35:19.427315+00:00
-- url     : https://prove2.me/theorems/a47fc1e3-018b-4048-a943-f94fbc103ef4
-- title:
--   A function with exponentially small derivative has a limit at $+\infty$
-- statement:
--   Let $\delta>0$, $C,s_0\in\mathbb R$, and let $m:\mathbb R\to\mathbb R$ be differentiable on $(s_0,\infty)$ with $|m'(s)|\le Ce^{-\delta s}$ for $s>s_0$. Then $\lim_{s\to\infty}m(s)$ exists in $\mathbb R$.
--
--   Formalization Note: the derivative is a function `m'` with `HasDerivAt m (m' s) s` for `s > s₀`; the conclusion is `∃ d, Tendsto m atTop (𝓝 d)`.
-- source:
--   Standard

import Mathlib

namespace Real

open Filter Topology

/-- If `m` has derivative `m'` at every `s > s₀` and `|m' s| ≤ C exp (-(δ s))` there, with
`δ > 0`, then `m` converges at `+∞`. -/
theorem exists_tendsto_of_abs_deriv_le_mul_exp {m m' : ℝ → ℝ} {s₀ C δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ s > s₀, HasDerivAt m (m' s) s)
    (hb : ∀ s > s₀, |m' s| ≤ C * Real.exp (-(δ * s))) :
    ∃ d : ℝ, Tendsto m atTop (𝓝 d) := by
  sorry

end Real
