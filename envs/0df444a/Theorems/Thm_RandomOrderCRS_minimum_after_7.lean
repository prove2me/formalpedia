-- Prove2me | Theorems.Thm_RandomOrderCRS_minimum_after_7
-- name    : RandomOrderCRS.minimum_after_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:15.515207+00:00
-- url     : https://prove2.me/theorems/55b24d44-f5a6-4b2d-bddc-8a48e648437f
-- title:
--   §3.1, after equation (7) — the minimum over $x_e$ is $c^*$
-- statement:
--   Consider, for $a=a_1$ and $x\in[0,1]$, the function
--
--   $$F(x):=a(x)\int_0^1e^{-2y(1-x)}\big(1+a(1)(1-x)y^2\big)\,dy.$$
--
--   Its minimum on $[0,1]$ occurs at $x=0$, where it takes the value $c^*=(e^2-4e^3+e^4+20e-22)/(4e^2)$, and $c^*\ge0.474035$.
--
--   This is the last step of the proof of Theorem 3. It contains no graph.
--
--   Differences from the source:
--   - encoding: the minimum occurs at $x_e=0$ when it takes on the value $c^*$ → $c^*\le F(x)$ on $[0,1]$, and $F(0)=c^*$; reason: the same statement
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, §3.1, after equation (7), p.22

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace RandomOrderCRS

/-- MacRury, Ma & Grammel, arXiv:2209.07520v2, §3.1, after equation (7), p.22, for `a = a₁`: "Upon
evaluating the integral in (7), we get a function of x_e whose minimum occurs at x_e = 0 when it
takes on the value (e²−4e³+e⁴+20e−22)/(4e²) ≥ 0.474035."
1. `c*` is a lower bound of the function on `[0, 1]`;
2. the value at `0` is `c*`;
3. `c* ≥ 0.474035`. -/
theorem minimum_after_7 :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      cStar ≤ a₁ t * ∫ y in (0 : ℝ)..1, exp (-2 * y * (1 - t)) * (1 + a₁ 1 * (1 - t) * y ^ 2)) ∧
    (a₁ 0 * ∫ y in (0 : ℝ)..1, exp (-2 * y * (1 - 0)) * (1 + a₁ 1 * (1 - 0) * y ^ 2)) = cStar ∧
    (0.474035 : ℝ) ≤ cStar := by sorry

end RandomOrderCRS
