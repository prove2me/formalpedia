-- Prove2me | Theorems.Thm_RegLearnGames_IndivRegret_theorem_11_variation_bound
-- name    : RegLearnGames.IndivRegret.theorem_11_variation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:21.065479+00:00
-- url     : https://prove2.me/theorems/464a0f73-b321-4472-bfbd-4c4b6123d48e
-- title:
--   Proof of Theorem 11, p. 5 — ‖uᵢ − uᵢ′‖²_* ≤ (n−1)Σ_{j≠i}‖wⱼ − wⱼ′‖² ≤ (n−1)²κ²
-- statement:
--   Consider an $n$-player game in which every player has $d$ strategies and utilities $u_i(s)\in[0,1]$. Let $w=(w_1,\dots,w_n)$ and $w'=(w'_1,\dots,w'_n)$ be two mixed profiles, and let $\kappa$ bound every player's movement: $\|w_j-w'_j\|_1\le\kappa$ for all $j$. Write $u_i$ and $u'_i$ for player $i$'s utility vectors against $w$ and against $w'$. Then for every player $i$,
--   $$\|u_i-u'_i\|_\infty^2\ \le\ (n-1)\sum_{j\ne i}\|w_j-w'_j\|_1^2\ \le\ (n-1)^2\kappa^2 .$$
--
--   Applied to consecutive profiles $w^{t-1},w^t$ of a repeated game, this bounds the variation of player $i$'s utilities by the movement of the other players; summed over $t=1,\dots,T$ it turns the RVU property into the regret bound of Theorem 11.
--
--   **Formalization Note** The movement bound is assumed for every player $j$, including $j=i$, as in the stability property of Theorem 11, which holds for all players.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, §3.2, the display after Theorem 11 ("Similar reasoning as in Theorem 4 yields")

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.IndivRegret

theorem theorem_11_variation_bound {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ)
    (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d)) (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d))
    (κ : ℝ) (hκ : ∀ j, RegLearnGames.TotalRegret.l1 (w j - w' j) ≤ κ) :
    ∀ i, ‖RegLearnGames.TotalRegret.utilVec u w i - RegLearnGames.TotalRegret.utilVec u w' i‖ ^ 2 ≤
        ((n : ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ∧
      ((n : ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, RegLearnGames.TotalRegret.l1 (w j - w' j) ^ 2 ≤
        ((n : ℝ) - 1) ^ 2 * κ ^ 2 := by sorry

end RegLearnGames.IndivRegret
