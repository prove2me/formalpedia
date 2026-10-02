-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_eq17_18_choiceProb_partials
-- name    : StochFictPlay.Supermodular.eq17_18_choiceProb_partials
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-28T10:19:40.462757+00:00
-- url     : https://prove2.me/theorems/edad0fc3-5f66-45b8-a989-bc395ddeb87d
-- title:
--   Eqs. (17)–(18) — sign properties of the derivative of a random utility choice function
-- statement:
--   Let $C$ be the choice function of a shock density $f$ on $\mathbb R^m$ satisfying the conditions of Theorem 2.1. Then for every payoff vector $\pi$,
--   $$\text{(17)}\quad \sum_{i=1}^{k} \sum_{j=1}^{l} \frac{\partial C_i}{\partial \pi_j}(\pi) > 0 \ \text{ for all } k, l < m,$$
--   $$\text{(18)}\quad \sum_{j=1}^{m} \frac{\partial C_i}{\partial \pi_j}(\pi) = 0 \ \text{ for all } i \le m.$$
--
--   These are the only two properties of the choice function that the proof of Theorem 5.1 uses; symmetry of $DC$ is not needed for supermodular games.
--
--   **Formalization Note** Strategies are 0-based: the paper's $k < m$ is index $k$ with $k + 1 < m$, and $\sum_{i=1}^k$ is the sum over indices $\le k$. The page leaves the argument $\pi$ implicit; both properties are stated at every $\pi$. $\partial C_i/\partial\pi_j(\pi)$ is the $i$-th entry of the Fréchet derivative of $C$ at $\pi$ applied to the $j$-th basis vector.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 30, eqs. (17) and (18)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Equations (17) and (18) (Hofbauer–Sandholm 2002, manuscript p. 30): the two properties of a
random utility choice function `C = choiceProb f` used to prove Theorem 5.1. At every payoff
vector `π ∈ ℝ^m`,

(17) `∑_{i=1}^{k} ∑_{j=1}^{l} ∂C_i/∂π_j (π) > 0` for all `k, l < m`, and

(18) `∑_{j=1}^{m} ∂C_i/∂π_j (π) = 0` for all `i ≤ m`.

Strategies are 0-based: the paper's `k < m` (1-based) is `k.val + 1 < m`, and `∑_{i=1}^{k}` is the
sum over `i ≤ k`. The page leaves the argument `π` implicit; both hold at every `π`.
`∂C_i/∂π_j (π)` is the `i`-th coordinate of the Fréchet derivative of `C` at `π` applied to the
`j`-th basis vector. -/
theorem eq17_18_choiceProb_partials (m : ℕ) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin m → ℝ) :
    (∀ k l : Fin m, k.val + 1 < m → l.val + 1 < m →
      0 < ∑ i : Fin m, ∑ j : Fin m,
        (if i ≤ k ∧ j ≤ l then fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i else 0)) ∧
    (∀ i : Fin m, ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0) := by sorry

end StochFictPlay.Supermodular
