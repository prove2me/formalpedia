-- Prove2me | Theorems.Thm_Real_exp_decay_of_sq_mul_le_second_deriv
-- name    : Real.exp_decay_of_sq_mul_le_second_deriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:33:08.393236+00:00
-- url     : https://prove2.me/theorems/ba864a90-0d1a-4ee3-babb-ebfb6b7ce2e3
-- title:
--   Decay of a nonnegative function with $f''\ge c^2f$ that tends to $0$
-- statement:
--   Let $c>0$, $s_0\in\mathbb R$, and let $f:\mathbb R\to\mathbb R$ be twice differentiable on $[s_0,\infty)$ (derivatives $f'=f_1$, $f_1'=f_2$ there) with
--   $$f\ge0,\qquad f(s)\to0\ (s\to\infty),\qquad f_2\ge c^2f\quad\text{on }[s_0,\infty).$$
--   Then $f_1\le0$ on $[s_0,\infty)$, and $f(s)\le f(s_0)\,e^{-c(s-s_0)}$ for all $s\ge s_0$.
--
--   This is the one-variable decay estimate used for $L^2$-norms of solutions on half-cylinders, where $f''\ge c^2f$ comes from a spectral gap.
--
--   Formalization Note: derivatives are given as functions `f1`, `f2` with `HasDerivAt` at every `s ≥ s0`.
-- source:
--   Standard (ODE theory)

import Mathlib

namespace Real

open Filter Topology

/-- Let `f` have derivative `f1` and `f1` have derivative `f2` on `[s0, ∞)`, with `f ≥ 0`,
`f → 0` at `+∞`, and `c² f ≤ f2` there for some `c > 0`. Then `f1 ≤ 0` on `[s0, ∞)` and
`f s ≤ f s0 * exp (-(c (s - s0)))` for `s ≥ s0`. -/
theorem exp_decay_of_sq_mul_le_second_deriv (f f1 f2 : ℝ → ℝ) (s0 c : ℝ) (hc : 0 < c)
    (hf : ∀ s ≥ s0, HasDerivAt f (f1 s) s) (hf1 : ∀ s ≥ s0, HasDerivAt f1 (f2 s) s)
    (hpos : ∀ s ≥ s0, 0 ≤ f s) (hlim : Tendsto f atTop (𝓝 0))
    (h2 : ∀ s ≥ s0, c ^ 2 * f s ≤ f2 s) :
    (∀ s ≥ s0, f1 s ≤ 0) ∧ ∀ s ≥ s0, f s ≤ f s0 * Real.exp (-(c * (s - s0))) := by
  sorry

end Real
