-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_gradient_rate
-- name    : SlowConvergence.SteepestDescent.gradient_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:32.856142+00:00
-- url     : https://prove2.me/theorems/8375c143-2564-4515-8cbd-55ac50267882
-- title:
--   §2 (2.10), pp. 3–4 — $\eta = \frac{1}{2-\tau}-\frac12 = \frac{\tau}{4-2\tau} > 0$ and $|g_k| = (1/(k+1))^{1/(2-\tau)}$
-- statement:
--   Let $0 < \tau < 1$, let $\eta = \tau/(4-2\tau)$, and let $g_k = -\big(\tfrac{1}{k+1}\big)^{\frac12+\eta}$ be the prescribed gradients (2.9) of the slow steepest-descent example. Then
--   $$\eta = \frac{1}{2-\tau} - \frac12 > 0 \qquad\text{and}\qquad |g_k| = \Big(\frac{1}{k+1}\Big)^{\frac{1}{2-\tau}} \quad \text{for every } k \ge 0.$$
--   This is (2.10) together with the remark that the first part of (2.9) gives the target rate (2.3), $\|g_k\| \ge (1/(k+1))^{1/(2-\tau)}$, by construction — here with equality. It is the step that fixes the rate of the example.
--
--   **Formalization Note** The paper allows any $\tau > 0$ for which $\eta$ is defined; the mission works with $\tau \in (0,1)$ throughout, the range the main theorem needs.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, pp. 3–4, §2, (2.3), (2.9), (2.10)

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, (2.10) and the sentence after it, pp. 3–4:
`η(τ) = 1/(2 − τ) − 1/2 = τ/(4 − 2τ) > 0`, and the first part of (2.9) gives (2.3) by construction,
with equality: `|g_k| = (1/(k+1))^{1/2+η} = (1/(k+1))^{1/(2−τ)}` for every `k ≥ 0`. -/
theorem gradient_rate (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    1 / (2 - τ) - 1 / 2 = SlowConvergence.Newton.eta τ ∧ 0 < SlowConvergence.Newton.eta τ ∧
      ∀ k : ℕ, |gk τ k| = (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) := by sorry

end SlowConvergence.SteepestDescent
