-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_tsitsiklis_van_roy_divergence
-- name    : SuttonBartoRL.OffPolicy.tsitsiklis_van_roy_divergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:22:00.606985+00:00
-- url     : https://prove2.me/theorems/2cad423e-c5a4-432c-ad0f-abf22a6dad8f
-- title:
--   Example 11.1 (11.10) — Tsitsiklis and Van Roy's counterexample diverges
-- statement:
--   In Tsitsiklis and Van Roy's counterexample the first state has estimated value $w$ and the second $2w$; the second state returns to itself with probability $1-\varepsilon$ and terminates with probability $\varepsilon$; all rewards are $0$. Setting $w_{k+1}$ at each step to the least-squares fit of the expected one-step return gives the objective of (11.10),
--   $$
--   J_c(w) = (w - \gamma\,2c)^2 + \bigl(2w - (1-\varepsilon)\gamma\,2c\bigr)^2, \qquad c = w_k .
--   $$
--   Let $0\le\varepsilon\le1$ and $0\le\gamma\le 1$. Then
--
--   1. for every $c\in\mathbb R$, $J_c$ has the unique minimizer $\displaystyle w = \frac{6-4\varepsilon}{5}\,\gamma c$;
--   2. if every $w_{k+1}$ minimizes $J_{w_k}$, $\gamma > \dfrac{5}{6-4\varepsilon}$ and $w_0\ne0$, then $|w_k|\to\infty$.
--
--   The example shows that even an exact least-squares fit at every step does not make DP with linear function approximation stable.
--
--   **Formalization Note** The book writes the first line of (11.10) as minimizing "the VE" over the two states, but its displayed objective is the unweighted sum in the second line; that displayed sum is what is formalized. The $\varepsilon$-transition goes to the terminal state, whose value is $0$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Example 11.1, Eq. (11.10), p. 263

import Mathlib

open Filter

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), Example 11.1 (Tsitsiklis and Van Roy's counterexample), Eq. (11.10),
p. 263. With the least-squares objective displayed in the second line of (11.10),
`J_c(w) = (w − γ·2c)² + (2w − (1 − ε)γ·2c)²` (`c = w_k` the previous weight), for `ε ∈ [0, 1]` and
`γ ∈ [0, 1]`:
1. `J_c` has the unique minimizer `((6 − 4ε)/5) γ c` over `w ∈ ℝ`;
2. if each `w_{k+1}` minimizes `J_{w_k}`, `γ > 5/(6 − 4ε)` and `w_0 ≠ 0`, then `|w_k| → ∞`. -/
theorem tsitsiklis_van_roy_divergence (ε γ : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ c u : ℝ,
      (∀ v : ℝ, (u - γ * (2 * c)) ^ 2 + (2 * u - (1 - ε) * γ * (2 * c)) ^ 2
          ≤ (v - γ * (2 * c)) ^ 2 + (2 * v - (1 - ε) * γ * (2 * c)) ^ 2)
        ↔ u = (6 - 4 * ε) / 5 * γ * c) ∧
    (∀ w : ℕ → ℝ,
      (∀ k (v : ℝ),
        (w (k + 1) - γ * (2 * w k)) ^ 2 + (2 * w (k + 1) - (1 - ε) * γ * (2 * w k)) ^ 2
          ≤ (v - γ * (2 * w k)) ^ 2 + (2 * v - (1 - ε) * γ * (2 * w k)) ^ 2) →
      5 / (6 - 4 * ε) < γ → w 0 ≠ 0 →
      Tendsto (fun k => |w k|) atTop atTop) := by sorry

end SuttonBartoRL.OffPolicy
