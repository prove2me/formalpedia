-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_homogeneous_majority_main_simple_solution
-- name    : TheoryOfGames.SimpleGames.homogeneous_majority_main_simple_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:09:39.757248+00:00
-- url     : https://prove2.me/theorems/4c16f796-5b0d-4d6c-8657-e981f6e43889
-- title:
--   (50:K) — every homogeneous weighted majority game possesses a main simple solution, and conversely under (50:20)
-- statement:
--   Let $v$ be the characteristic function (25:3:a)–(25:3:c) of a simple game $\Gamma$ with $n$ players in the reduced form with $\gamma = 1$, so that $v((i)) = -1$ for all $i$ (50.4.1), and let $W^m$ be its set of minimal winning coalitions. For numbers $x_1, \dots, x_n$ let $V$ be the set of all $\vec\alpha^S$, $S$ in $W^m$, where $\alpha^S_i = -1$ for $i$ not in $S$ and $\alpha^S_i = -1 + x_i$ for $i$ in $S$. When
--   $$\text{(50:17)}\ \ \sum_{i \in S} x_i = n \ \text{ for all } S \text{ in } W^m, \qquad \text{(50:7)}\ \ x_i \geqq 0,$$
--   $V$ is called a **main simple solution** (50.8.1).
--
--   1. Every homogeneous weighted majority game possesses a main simple solution. Precisely: let $w_1, \dots, w_n$ be weights for $\Gamma$ — they fulfil (50:B) and $W_\Gamma$ is the set of $S$ with $\sum_{i \in S} w_i > \tfrac12 \sum_i w_i$ — which are homogeneous, with common value $a$ of $a_S = 2\sum_{i\in S} w_i - \sum_i w_i$ on $W^m$ (50:E). Put
--   $$b = \tfrac12\Big(\sum_{i=1}^n w_i + a\Big), \qquad x_i = \frac nb\, w_i .$$
--   Then the $x_i$ fulfil (50:7) and (50:17), and $V$ is a solution.
--   2. Conversely, if numbers $x_i$ fulfil (50:7) and (50:17) — the game possesses a main simple solution — then $w_i \equiv x_i$ are homogeneous weights for $\Gamma$ if and only if
--   $$\text{(50:20)}\qquad \sum_{i=1}^n x_i < 2n.$$
--
--   The result connects the numerical description of simple games by homogeneous weights with the finite solutions built from the minimal winning coalitions; it is the capstone of §50.
--
--   **Formalization Note** The game is fixed by its reduced ($\gamma = 1$) characteristic function, the normalization §50 works in; any simple game with the given $W_\Gamma$ has exactly one such $v$ (49:2). The number $b$ of (50:18) is $\tfrac12(\sum w_i + a)$ as on p. 444. In part 1 the $x_i$ are defined for every player, including players in no minimal winning coalition, for whom the book defines none; their values do not enter any $\vec\alpha^S$. In part 2 the derived weights are $w_i = x_i$ for every player (the book's footnote 2 on p. 444 alternatively sets the weight of such players to $0$), and (50:20) is summed over all players as printed. "Weights for the game" means (50:B) together with $W_\Gamma$ equal to the $W$ of (50:1).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 444, (50:K), (50:18)–(50:20); p. 443, 50.8.1, (50:17), (50:7); p. 435, (50:E); p. 433, (50:B)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:K), p. 444. Let `v` be the characteristic function of a simple game in the reduced form
with `γ = 1` (`v((i)) = -1`), `W^m` its minimal winning coalitions.
1. Every homogeneous weighted majority game possesses a main simple solution: if `w` are weights
   for the game (50:B), (50:1) with common value `a` of the `a_S`, `S` in `W^m` (50:E), then
   `xᵢ = (n / b) wᵢ` with `b = ½ (∑ wᵢ + a)` (50:18) fulfils (50:7), (50:17), and the set of all
   `α^S`, `S` in `W^m`, is a solution.
2. Conversely, if `x` fulfils (50:7) and (50:17) (the game possesses a main simple solution),
   then `wᵢ ≡ xᵢ` are homogeneous weights for the game if and only if (50:20)
   `∑_{i=1}^n xᵢ < 2n`. -/
theorem homogeneous_majority_main_simple_solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1) :
    (∀ (w : Fin n → ℝ) (a : ℝ), IsWeightsFor v w →
        (∀ S ∈ minimalSets (winningSets v), advantage w S = a) →
        (∀ i, 0 ≤ (n : ℝ) / (((∑ j, w j) + a) / 2) * w i) ∧
        (∀ S ∈ minimalSets (winningSets v),
          ∑ i ∈ S, (n : ℝ) / (((∑ j, w j) + a) / 2) * w i = (n : ℝ)) ∧
        IsSolution v (mainSet (minimalSets (winningSets v))
          (fun i => (n : ℝ) / (((∑ j, w j) + a) / 2) * w i))) ∧
    (∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
        (∀ S ∈ minimalSets (winningSets v), ∑ i ∈ S, x i = (n : ℝ)) →
        ((IsWeightsFor v x ∧ IsHomogeneous x) ↔ ∑ i, x i < 2 * (n : ℝ))) := by sorry

end TheoryOfGames.SimpleGames
