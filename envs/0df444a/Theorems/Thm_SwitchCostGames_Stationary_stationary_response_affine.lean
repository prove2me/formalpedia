-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_stationary_response_affine
-- name    : SwitchCostGames.Stationary.stationary_response_affine
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:14.005468+00:00
-- url     : https://prove2.me/theorems/7c617fe3-d0d6-4cea-abfb-48e9f7e1f4cb
-- title:
--   Proof of Theorem 1 — against a fixed stationary strategy of player 2, player 1's best payoff $f(c)$ is affine in $c$, attained by one stationary strategy
-- statement:
--   Let $\Gamma = (A,S,\cdot)$ be a game with switching costs with $m,n\ge1$, and let $\tau$ be a stationary strategy of player 2, held fixed as the switching-cost weight $c$ varies. Then there are real numbers $\alpha,\beta$ and a stationary strategy $\sigma$ of player 1, all independent of $c$, such that for every $c \ge 0$:
--
--   1. $\gamma_c(\sigma, \tau) = \alpha + \beta c$;
--   2. $\gamma_c(\sigma', \tau) \le \alpha + \beta c$ for every behavior strategy $\sigma'$ of player 1.
--
--   In other words, player 1's best-response payoff against $\tau$,
--   $$
--   f(c) = \alpha + \beta c ,
--   $$
--   is a linear function of $c$, and a single stationary best response works for all $c$. In the paper this is applied to an optimal stationary strategy $\sigma_{c^*}$ of player 2 at an interior point $c^*$ of a segment where $v$ is linear; comparing $v(c) \le f_{c^*}(c)$ with equality at $c^*$ yields the robust optimal strategy of Theorem 1.
--
--   **Formalization Note** The paper argues for player 2's optimal strategy $\sigma_{c^*}$, but the argument uses only that it is stationary, so the statement is made for every stationary $\tau$. No sign is asserted for $\beta$.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 3 (PDF 5), proof of Theorem 1, third paragraph

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem stationary_response_affine {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n)
    (τ : Strategy2 m n) (hτ : IsStationary2 τ) :
    ∃ α β : ℝ, ∃ σ : Strategy1 m n, IsStationary1 σ ∧ ∀ c : ℝ, 0 ≤ c →
      payoff G c σ τ = α + β * c ∧ ∀ σ' : Strategy1 m n, payoff G c σ' τ ≤ α + β * c := by sorry

end SwitchCostGames.Stationary
