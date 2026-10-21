-- Prove2me | Theorems.Thm_ParamMCF_MCA_max_f2_eq
-- name    : ParamMCF.MCA.max_f2_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:13.536652+00:00
-- url     : https://prove2.me/theorems/a673d882-06ab-4334-8368-e3dca70e5a7b
-- title:
--   Proof of Theorem 5, p. 18 — under (ii) the maximum of |f″| on a mesh interval is attained at an endpoint
-- statement:
--   Let $f$ be a marginal cost whose first and second derivatives are differentiable, and assume the shape condition of Theorem 5 (ii): $f''$ is non-decreasing with $f''\ge0$ on $[0,\infty)$, and non-increasing with $f''\le0$ on $(-\infty,0)$. Then for every interval $[x_i,x_{i+1}]$ of a strictly increasing mesh
--
--   $$\max_{\xi\in[x_i,x_{i+1}]}|f''(\xi)|=\max\{|f''(x_i)|,|f''(x_{i+1})|\}.$$
--
--   With $B:=\max\{\sqrt{|f''(x_i)|},\sqrt{|f''(x_{i+1})|}\}$ the right-hand side is $B^2$; this is how step-size condition (ii) of Theorem 5 controls the interpolation error (18).
--
--   **Formalization Note** The maximum is written as the supremum of $|f''|$ over the image of the compact interval; $f''$ is differentiable, hence continuous, so the supremum is attained. The identity $\max\{\dots\}=B^2$ is immediate for the corrected $B$ (square roots on both terms) and is not restated.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 18, proof of Theorem 5, case (ii)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- Proof of Theorem 5, p. 18: under the shape condition of (ii), the maximum of `|f''|` over a mesh
interval `[x_i, x_{i+1}]` is attained at one of its endpoints. -/
theorem max_f2_eq (g : ℝ → ℝ) (hg : IsMarginalCost g)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0))
    (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (i : Fin K) :
    sSup ((fun ξ => |deriv (deriv g) ξ|) '' Set.Icc (xs i.castSucc) (xs i.succ)) =
      max |deriv (deriv g) (xs i.castSucc)| |deriv (deriv g) (xs i.succ)| := by sorry

end ParamMCF.MCA
