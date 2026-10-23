-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_eps_bounds
-- name    : PathoSubgrad.Circle.eps_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:33.938981+00:00
-- url     : https://prove2.me/theorems/47a0a3ab-a6eb-4f82-b25b-03655cb7a420
-- title:
--   §2.1, p. 6 — 2/(i+1) < ε_i < 1/i + 1/(i+1) + 1/(i log i) for large i; ε_i → 0, Σ ε_i = ∞, Σ ε_i² < ∞
-- statement:
--   Let $x_i$ and $\varepsilon_i=\|x_{i+1}-x_i\|$ be the points and step sizes of the example on the circle. For all sufficiently large $i$,
--   $$\frac{2}{i+1}<\varepsilon_i<\frac1i+\frac1{i+1}+\frac1{i\log i},$$
--   and consequently
--   $$\varepsilon_i\to0,\qquad\sum_i\varepsilon_i=+\infty,\qquad\sum_i\varepsilon_i^2<+\infty.$$
--
--   These are the step-size requirements of Definition 1 (and the classical square-summability), so the points $x_i$ can serve as a small-step subgradient sequence.
--
--   **Formalization Note.** The paper's chain ends with a further inequality "$<2/i$", which would require $\log i>i+1$ and is false for every $i$ (numerically $i\,\varepsilon_i\to2$ from above); it is omitted, and the three consequences still follow from the remaining bounds. "For large $i$" is $\exists N,\ \forall i\ge N$.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 6, §2.1 (unnumbered estimate on ε_i)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem eps_bounds :
    (∃ N : ℕ, ∀ i ≥ N, 2 / ((i : ℝ) + 1) < eps i ∧
      eps i < 1 / (i : ℝ) + 1 / ((i : ℝ) + 1) + 1 / ((i : ℝ) * Real.log i)) ∧
    Tendsto eps atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ i ∈ Finset.range N, eps i) atTop atTop ∧
    Summable (fun i => eps i ^ 2) := by sorry

end PathoSubgrad.Circle
