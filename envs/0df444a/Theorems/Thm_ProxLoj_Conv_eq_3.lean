-- Prove2me | Theorems.Thm_ProxLoj_Conv_eq_3
-- name    : ProxLoj.Conv.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:19.148983+00:00
-- url     : https://prove2.me/theorems/9abdf308-5a3b-4490-8725-810ccb6e0318
-- title:
--   (3), §2.2, p. 3 — a proximal step is an implicit subgradient step: x^{k+1} = x^k − λ_k g^{k+1} with g^{k+1} ∈ ∂f(x^{k+1})
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper, let $(\lambda_k)$ be positive step sizes, and let $(x^k)$ comply with the proximal algorithm (2), i.e. $x^{k+1}$ minimizes $u\mapsto f(u)+\frac1{2\lambda_k}|u-x^k|^2$. Then for every $k$ there is a limiting subgradient $g^{k+1}\in\partial f(x^{k+1})$ such that
--   $$x^{k+1}=x^k-\lambda_k g^{k+1}.\qquad(3)$$
--
--   This is the optimality condition of the proximal step: the algorithm is an implicit (backward) subgradient method, and $|g^{k+1}|=|x^{k+1}-x^k|/\lambda_k$ is the quantity the Łojasiewicz inequality controls.
--
--   **Formalization Note** Only properness and positivity of the steps are assumed; lower semicontinuity, (H1)–(H3), the bounds $\lambda_k\in(\lambda_-,\lambda_+)$ and boundedness of the sequence are not needed and are dropped. Properness is required: for $f\equiv+\infty$ every point is a minimizer and $\partial f$ is empty.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, p. 3, §2.2, display (3)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- (3), §2.2, p. 3: every proximal step is an implicit subgradient step,
`x^{k+1} = x^k - λ_k g^{k+1}` with `g^{k+1} ∈ ∂f(x^{k+1})` (limiting subdifferential). -/
theorem eq_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x) :
    ∀ k, ∃ g ∈ LimitingSubdiff f (x (k + 1)), x (k + 1) = x k - lam k • g := by sorry

end ProxLoj.Conv
