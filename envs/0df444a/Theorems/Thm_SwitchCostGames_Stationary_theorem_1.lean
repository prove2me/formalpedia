-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_theorem_1
-- name    : SwitchCostGames.Stationary.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:15.500151+00:00
-- url     : https://prove2.me/theorems/19b6f4d8-029a-41af-8da6-aa1bb84dd6a6
-- title:
--   Theorem 1 — the value $v(c)$ in stationary strategies exists and is continuous, increasing, concave, piecewise linear, eventually constant, with segment-robust optimal strategies
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$) and $S$ a real $n\times n$ matrix with nonnegative entries and $s_{jj}=0$. For a switching-cost weight $c \ge 0$ consider the repeated zero-sum game in which player 2 pays player 1 the stage payoff $a_{i(t)j(t)} + c\,s_{j(t-1)j(t)}$ (with $j(0)=1$), and the payoff of a strategy pair $(\sigma,\tau)$ is the lower limit of the expected average,
--   $$
--   \gamma_c(\sigma,\tau) = \liminf_{T\to\infty}\mathbb E_{\sigma,\tau}\Big(\frac1T\sum_{t=1}^T a_{i(t)j(t)} + c\,s_{j(t-1)j(t)}\Big).
--   $$
--   Then:
--
--   1. for every $c\ge0$ the game has a value $v(c)$ in stationary strategies (optimal stationary strategies of both players guarantee $v(c)$ against all behavior strategies of the opponent);
--   2. the function $c\mapsto v(c)$ is continuous, increasing, concave and piecewise linear on $[0,\infty)$;
--   3. $v$ is eventually constant: there is $C\ge0$ with $v(c) = v(C)$ for all $c\ge C$;
--   4. if $v$ is linear on an interval $[\underline c,\bar c]$ with $0\le\underline c<\bar c$, then player 2 has a single stationary strategy $\tau$ that is optimal for all $c \in [\underline c,\bar c]$: $\gamma_c(\sigma,\tau)\le v(c)$ for every behavior strategy $\sigma$ of player 1 and every such $c$.
--
--   Item 4 says that optimal play is robust: player 2 does not need to know the exact switching-cost weight within a linear piece of $v$.
--
--   **Formalization Note** "Increasing" is `MonotoneOn` (nondecreasing), since $v$ is eventually constant. "Linear on $[\underline c,\bar c]$" means affine there. The value is unique, so the existential over $v$ is not a loophole. The paper says "player 2 has a strategy"; the Lean statement requires that strategy to be stationary, which the paper's proof provides (it is an optimal strategy of the stochastic game, stationary by §2). A degenerate segment $\underline c = \bar c$ is excluded; it is covered by item 1.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 3 (PDF 5), Theorem 1

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem theorem_1 {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) :
    ∃ v : ℝ → ℝ,
      (∀ c : ℝ, 0 ≤ c → IsValue G c (v c)) ∧
      ContinuousOn v (Set.Ici 0) ∧ MonotoneOn v (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) v ∧
      IsPiecewiseAffineOn v (Set.Ici 0) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, C ≤ c → v c = v C) ∧
      (∀ cLo cHi : ℝ, 0 ≤ cLo → cLo < cHi →
        (∃ α β : ℝ, ∀ c ∈ Set.Icc cLo cHi, v c = α + β * c) →
        ∃ τ : Strategy2 m n, IsStationary2 τ ∧
          ∀ c ∈ Set.Icc cLo cHi, ∀ σ : Strategy1 m n, payoff G c σ τ ≤ v c) := by sorry

end SwitchCostGames.Stationary
