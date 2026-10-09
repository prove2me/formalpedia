-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_a_k_closed_form
-- name    : RelSmoothFOM.DualAvg.a_k_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:30.719323+00:00
-- url     : https://prove2.me/theorems/818549e5-ac8e-4e52-a81f-85ff6c84cba2
-- title:
--   Proof of Theorem 3.2, p. 347 — A_k = (1/μ)[(1 + μ/(L−μ))^k − 1] for μ > 0, and A_k = k/L for μ = 0
-- statement:
--   Let $0 \le \mu < L$ and let $a_{i+1} = \frac{1}{L-\mu}\left(\frac{L}{L-\mu}\right)^i$ be the weights of the dual averaging scheme, with partial sums $A_k = \sum_{i=0}^{k-1} a_{i+1}$. Then for every $k \ge 0$:
--
--   1. if $0 < \mu < L$,
--   $$A_k = \frac{1}{\mu}\left[\left(1 + \frac{\mu}{L-\mu}\right)^k - 1\right];$$
--   2. if $\mu = 0 < L$, then $A_k = k/L$.
--
--   This closed form converts the bound $h(x)/A_k$ produced by the proof of Theorem 3.2 into the explicit rate (32).
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 347, proof of Theorem 3.2, definition of A_k following (34)

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- Proof of Theorem 3.2, p. 347: the closed form of `A_k = Σ_{i=0}^{k−1} a_{i+1}`.
For `0 < μ < L`, `A_k = (1/μ)((1 + μ/(L − μ))^k − 1)`; for `μ = 0 < L`, `A_k = k/L`. -/
theorem a_k_closed_form (L μ : ℝ) :
    (0 < μ → μ < L → ∀ k : ℕ, daSum L μ k = ((1 + μ / (L - μ)) ^ k - 1) / μ) ∧
    (μ = 0 → 0 < L → ∀ k : ℕ, daSum L μ k = (k : ℝ) / L) := by sorry

end RelSmoothFOM.DualAvg
