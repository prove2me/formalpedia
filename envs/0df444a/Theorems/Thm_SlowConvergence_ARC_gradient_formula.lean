-- Prove2me | Theorems.Thm_SlowConvergence_ARC_gradient_formula
-- name    : SlowConvergence.ARC.gradient_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:06.293634+00:00
-- url     : https://prove2.me/theorems/511ff82d-b95d-49b7-8b94-d30b2e8d6f52
-- title:
--   §5, p. 13 — $\eta(\tau) = 2\tau/(9-6\tau) > 0$ and (5.4) gives (5.1): $|g_k| = (1/(k+1))^{2/(3-2\tau)}$
-- statement:
--   Let $0<\tau<1$ and $\eta = \tfrac12\big(\tfrac2{3-2\tau} - \tfrac23\big)$. Then
--   $$\eta = \frac{2\tau}{9-6\tau} > 0, \qquad \frac23 + 2\eta = \frac2{3-2\tau},$$
--   and the prescribed gradients $g_k = -(1/(k+1))^{\frac23+2\eta}$ of (5.4) satisfy (5.1):
--   $$|g_k| = \Big(\frac1{k+1}\Big)^{\frac2{3-2\tau}} \qquad\text{for all } k\ge0 .$$
--
--   This is the rate that, through the iteration count, makes ARC need about $\epsilon^{-3/2+\tau}$ iterations.
--
--   **Formalization Note** The paper says "for any $\tau>0$"; the construction needs $\tau<1$, which is assumed here as everywhere in the mission.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 13, §5, (5.1), (5.4) and η(τ)

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §5, p. 13: "where now η = η(τ) def= ½(2/(3 − 2τ) − 2/3)
= 2τ/(9 − 6τ) > 0. Observe that (5.4) gives (5.1) by construction." For `0 < τ < 1`,
`η = 2τ/(9 − 6τ) > 0`, `2/3 + 2η = 2/(3 − 2τ)`, and the prescribed gradients `g_k` of (5.4) satisfy
(5.1): `|g_k| = (1/(k+1))^{2/(3−2τ)}` for all `k ≥ 0`. -/
theorem gradient_formula (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    eta τ = 2 * τ / (9 - 6 * τ) ∧ 0 < eta τ ∧ 2 / 3 + 2 * eta τ = 2 / (3 - 2 * τ) ∧
      ∀ k : ℕ, |gk τ k| = (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ)) := by sorry

end SlowConvergence.ARC
