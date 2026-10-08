-- Prove2me | Theorems.Thm_RWPI_SqrtLasso_eq_29_minimization
-- name    : RWPI.SqrtLasso.eq_29_minimization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:28:33.805783+00:00
-- url     : https://prove2.me/theorems/f6f29a23-ed6e-42e5-b661-a99cda14cada
-- title:
--   (29) and the display after it — $\inf_{\gamma>b^2}\{\gamma\delta + \frac{\gamma}{\gamma-b^2}M\} = (\sqrt M + b\sqrt\delta)^2$
-- statement:
--   Let $M\ge0$, $b\ge0$ and $\delta\ge0$ be real numbers. Then
--
--   $$
--   \inf_{\gamma > b^2}\Big\{ \gamma\delta + \frac{\gamma}{\gamma-b^2}\,M \Big\} = \big(\sqrt M + b\sqrt\delta\big)^2 .
--   $$
--
--   In the proof of Proposition 2, $M = \mathrm{MSE}_n(\beta)$ and $b = \|\bar\beta\|_p$; the right side of (29) is this infimum, and the identity turns it into $(\sqrt{\mathrm{MSE}_n(\beta)}+\sqrt\delta\|\bar\beta\|_p)^2$. The same computation, with $b = \|\beta\|_p$, finishes Theorem 1.
--
--   The identity includes the degenerate cases $b = 0$, $M = 0$ and $\delta = 0$, in which the objective does not grow to $\infty$ at both ends of the interval and the infimum need not be attained.
--
--   **Formalization Note** Stated as `IsGLB` of the set of values $\{\gamma\delta + \frac{\gamma}{\gamma-b^2}M : \gamma > b^2\}$, i.e. the right side is the greatest lower bound; no junk value of a real infimum is involved.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 29, App. A.1, proof of Proposition 2, (29) and the display after it

import Mathlib

namespace RWPI.SqrtLasso

/-- The one-dimensional minimization behind (29) and the display after it (App. A.1, proof of
Proposition 2, p. 29): for `M ≥ 0` (the mean square error), `b ≥ 0` (the dual norm `‖β̄‖_p`) and
`δ ≥ 0`, the infimum of `γδ + γ/(γ − b²)·M` over `γ > b²` is `(√M + b√δ)²`. Stated as a greatest
lower bound, so no junk value of a real infimum is involved; the degenerate cases `b = 0`, `M = 0`,
`δ = 0` (where the infimum need not be attained) are included. -/
theorem eq_29_minimization (M b δ : ℝ) (hM : 0 ≤ M) (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    IsGLB {v : ℝ | ∃ γ : ℝ, b ^ 2 < γ ∧ v = γ * δ + γ / (γ - b ^ 2) * M}
      ((Real.sqrt M + b * Real.sqrt δ) ^ 2) := by sorry

end RWPI.SqrtLasso
