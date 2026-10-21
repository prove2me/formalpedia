-- Prove2me | Theorems.Thm_ParamMCF_MCA_eq_18
-- name    : ParamMCF.MCA.eq_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:13.061158+00:00
-- url     : https://prove2.me/theorems/fa95c9e4-819b-4120-95d6-586b1167e0ed
-- title:
--   Equation (18), p. 17 — one eighth linear spline error bound
-- statement:
--   Let $f$ have two derivatives on the real line, and let $s_f$ be its linear spline on a strictly increasing mesh. On a mesh interval $[x_i,x_{i+1}]$ of width $\delta_i$, if $|f''(\xi)|\le M$ throughout that interval, then for every $x$ in it,
--
--   $$|f(x)-s_f(x)|\le\frac18\delta_i^2 M.\tag{18}$$
--
--   This quantitative interpolation bound links mesh widths to the marginal cost comparisons of Lemma 4.
--
--   **Formalization Note** The bound form avoids taking a real supremum of an unbounded second derivative; whenever the maximum in the paper exists, $M$ can be chosen as that maximum.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 17, (18)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- The linear-spline interpolation bound (18), p. 17, in bounded-second-derivative form. -/
theorem eq_18 (g : ℝ → ℝ)
    (hg : Differentiable ℝ g ∧ Differentiable ℝ (deriv g))
    (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (i : Fin K) (x M : ℝ)
    (hx : x ∈ Set.Icc (xs i.castSucc) (xs i.succ))
    (hM : ∀ ξ ∈ Set.Icc (xs i.castSucc) (xs i.succ), |deriv (deriv g) ξ| ≤ M) :
    |g x - linSpline K xs g x| ≤
      (1 / 8 : ℝ) * (xs i.succ - xs i.castSucc) ^ 2 * M := by sorry

end ParamMCF.MCA
