-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_lemma_1
-- name    : SwitchCostGames.Stationary.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:12.320705+00:00
-- url     : https://prove2.me/theorems/55c96ba8-6c54-4253-96ba-f81efe89a676
-- title:
--   Lemma 1 — the value of the parametric one-shot game with payoff $a_{ij} + b_j x_j$ is continuous, increasing, concave and piecewise linear in every direction
-- statement:
--   Let $A = (a_{ij})$ be a real matrix with nonempty finite sets of rows and columns, and let $b_1,\dots,b_n \ge 0$. For every $x = (x_1,\dots,x_n) \in \mathbb R^n$ let $\Gamma(x)$ be the one-shot zero-sum game with payoff matrix
--   $$
--   a_{ij} + b_j x_j ,
--   $$
--   and let $v(x)$ be its value. Then the value function $v : \mathbb R^n \to \mathbb R$
--
--   1. is continuous;
--   2. is increasing in every parameter: $x \le x'$ coordinatewise implies $v(x) \le v(x')$;
--   3. is concave;
--   4. is piecewise linear in every direction: for every $x, d \in \mathbb R^n$ the function $t \mapsto v(x + t d)$ is piecewise linear on $\mathbb R$ with finitely many pieces.
--
--   The lemma is independent of the switching-cost model. In Theorem 1 it is applied to the one-shot game whose pure strategies are the pure stationary strategies of the repeated game, along the diagonal $x = (c,\dots,c)$.
--
--   **Formalization Note** The rows and columns are arbitrary nonempty finite types, so that the lemma applies to the one-shot game on pure stationary strategies. The value is passed as a function $v$ with the hypothesis that $v(x)$ is the saddle value of $\Gamma(x)$ for every $x$; this hypothesis is satisfiable for every $A$ and $b$ by von Neumann's minimax theorem, and it determines $v$ uniquely. "Increasing in every parameter" is `Monotone` for the coordinatewise order on $\mathbb R^n$.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 2 (PDF 4), §3.1, Lemma 1

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem lemma_1 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A : ι → κ → ℝ) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (v : (κ → ℝ) → ℝ) (hv : ∀ x, IsSaddleValue (paramGame A b x) (v x)) :
    Continuous v ∧ Monotone v ∧ ConcaveOn ℝ Set.univ v ∧
      ∀ x d : κ → ℝ, IsPiecewiseAffineOn (fun t : ℝ => v (x + t • d)) Set.univ := by sorry

end SwitchCostGames.Stationary
