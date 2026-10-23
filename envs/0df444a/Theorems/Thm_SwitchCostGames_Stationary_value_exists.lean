-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_value_exists
-- name    : SwitchCostGames.Stationary.value_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:22.279899+00:00
-- url     : https://prove2.me/theorems/81209e83-fe05-486e-9473-e4ebef69fddd
-- title:
--   §2 (Filar) — for every $c \ge 0$ the game with switching costs has a value in stationary strategies
-- statement:
--   Let $\Gamma = (A, S, c)$ be a zero-sum game with switching costs: $A$ a real $m\times n$ matrix with $m,n\ge1$, $S$ a nonnegative $n\times n$ matrix with zero diagonal, and $c \ge 0$. Then the repeated game with the undiscounted (liminf) average payoff $\gamma_c$ has a value $v$ in stationary strategies: there are stationary strategies $\sigma^*$ of player 1 and $\tau^*$ of player 2 such that
--   $$
--   \gamma_c(\sigma^*, \tau') \ \ge\ v \ \ge\ \gamma_c(\sigma', \tau^*)
--   $$
--   for every behavior strategy $\tau'$ of player 2 and every behavior strategy $\sigma'$ of player 1.
--
--   The game is a stochastic game whose state is the previous column of player 2; only player 2 controls the transitions, and the existence of the value in stationary strategies is Filar's theorem for single-controller stochastic games, as quoted in §2 of the paper. It provides the function $c \mapsto v(c)$ studied in Theorem 1.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 2 (PDF 4), §2 (citing Filar [2])

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem value_exists {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c : ℝ) (hc : 0 ≤ c) :
    ∃ v : ℝ, IsValue G c v := by sorry

end SwitchCostGames.Stationary
