-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_filar_raghavan
-- name    : SwitchCostGames.Stationary.filar_raghavan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:09.760986+00:00
-- url     : https://prove2.me/theorems/7dd66b49-adc6-4a36-8b1e-c5dc0a970511
-- title:
--   Proof of Theorem 1 (Filar–Raghavan) — the value equals the value of a one-shot game on pure stationary strategies with payoffs $a_{fg} + b_g c$, $b_g \ge 0$
-- statement:
--   Let $\Gamma = (A,S,c)$ be a zero-sum game with switching costs with $m,n\ge1$. A pure stationary strategy of player 1 is a map $f:[n]\to[m]$ and of player 2 a map $g:[n]\to[n]$ (the action to play after each previous column). There are real numbers $a_{fg}$, indexed by pairs of pure stationary strategies, and $b_g \ge 0$, indexed by the pure stationary strategies of player 2 alone, such that:
--
--   1. for every $c \ge 0$, whenever player 1 plays the pure stationary strategy $f$ and player 2 the pure stationary strategy $g$, the payoff of the repeated game is
--   $$
--   \gamma_c(f, g) = a_{fg} + b_g\, c ;
--   $$
--   2. for every $c \ge 0$ and every real $v$, $v$ is the value of the repeated game in stationary strategies if and only if $v$ is the value of the one-shot game whose row (column) strategies are the pure stationary strategies of player 1 (player 2) and whose payoff is $a_{fg} + b_g c$.
--
--   The coefficient of $c$ depends only on player 2's strategy because only player 2 bears switching costs, and it is nonnegative because it is a convex combination of entries of $S$. This is the reduction, due to Filar and Raghavan, that lets Lemma 1 be applied to the repeated game.
--
--   **Formalization Note** The one-shot game is the parametric game $\Gamma(x)$ of §3.1 with matrix $(a_{fg})$, coefficients $(b_g)$ and all parameters $x_g$ equal to $c$. Its pure strategies are `Fin n → Fin m` and `Fin n → Fin n`; here $a_{ij}, b_j$ in the paper's notation are indexed by pure stationary strategies, not by the rows and columns of $A$.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 3 (PDF 5), proof of Theorem 1, first paragraph (citing Filar and Raghavan [3])

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem filar_raghavan {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) :
    ∃ (a : (Fin n → Fin m) → (Fin n → Fin n) → ℝ) (b : (Fin n → Fin n) → ℝ),
      (∀ g, 0 ≤ b g) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ (f : Fin n → Fin m) (g : Fin n → Fin n)
          (σ : Strategy1 m n) (τ : Strategy2 m n),
          IsPureStationary1 σ f → IsPureStationary2 τ g → payoff G c σ τ = a f g + b g * c) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ v : ℝ, IsValue G c v ↔
          IsSaddleValue (paramGame a b (fun _ => c)) v) := by sorry

end SwitchCostGames.Stationary
