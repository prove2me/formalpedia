-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_eq_EC_2
-- name    : PriceQualityService.Oligopoly.eq_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:15.969197+00:00
-- url     : https://prove2.me/theorems/e32848e2-d5cb-4e4e-857d-7de79516d1d3
-- title:
--   (EC.2): the markup-weighted attraction is unimodal in price, with peak at markup $r_i+1$
-- statement:
--   Fix real numbers $\alpha_i, a_i, b_i, c_i, s_i$ (the parameters of product $i$), a quality $q_i$, a duration $t_i$ and a level $r_i$. Let
--   $$
--   g(p_i) = \big[p_i - c_i q_i^2 - t_i(a_i - b_i q_i) - r_i\big] \exp(\alpha_i q_i - p_i + t_i s_i).
--   $$
--   Then $g$ is strictly increasing on $(-\infty, p_i^\circ]$ and strictly decreasing on $[p_i^\circ, \infty)$, where $p_i^\circ = c_i q_i^2 + t_i(a_i - b_i q_i) + r_i + 1$, and its maximum value is
--   $$
--   g(p_i^\circ) = \exp\big(\alpha_i q_i - c_i q_i^2 - t_i(a_i - b_i q_i - s_i) - r_i - 1\big).
--   $$
--
--   This eliminates the price from firm $i$'s best-response problem: the optimal price sets the markup over cost to $r_i + 1$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 2 (PDF p. 35), (EC.2)

import Mathlib

namespace PriceQualityService.Oligopoly

/-- (EC.2), Online Supplement p. 2: for given `q_i`, `t_i` and `r_i`, the function
`p_i ↦ [p_i − c_i q_i² − t_i(a_i − b_i q_i) − r_i] · exp(α_i q_i − p_i + t_i s_i)` is unimodal:
strictly increasing up to `p_i = c_i q_i² + t_i(a_i − b_i q_i) + r_i + 1`, strictly decreasing
after it, and its maximum value is `exp(α_i q_i − c_i q_i² − t_i(a_i − b_i q_i − s_i) − r_i − 1)`.
The parameters of the single product `i` are written as real numbers. -/
theorem eq_EC_2 (α a b c s q t r : ℝ) :
    StrictMonoOn
        (fun p : ℝ => (p - c * q ^ 2 - t * (a - b * q) - r) * Real.exp (α * q - p + t * s))
        (Set.Iic (c * q ^ 2 + t * (a - b * q) + r + 1)) ∧
      StrictAntiOn
        (fun p : ℝ => (p - c * q ^ 2 - t * (a - b * q) - r) * Real.exp (α * q - p + t * s))
        (Set.Ici (c * q ^ 2 + t * (a - b * q) + r + 1)) ∧
      ((c * q ^ 2 + t * (a - b * q) + r + 1) - c * q ^ 2 - t * (a - b * q) - r) *
          Real.exp (α * q - (c * q ^ 2 + t * (a - b * q) + r + 1) + t * s) =
        Real.exp (α * q - c * q ^ 2 - t * (a - b * q - s) - r - 1) := by sorry

end PriceQualityService.Oligopoly
