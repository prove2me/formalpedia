-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_theorem_4_variation_bound
-- name    : RegLearnGames.TotalRegret.theorem_4_variation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:10.298312+00:00
-- url     : https://prove2.me/theorems/8706722a-1407-47db-851f-f288a755670f
-- title:
--   Proof of Theorem 4, display after “so that”, p. 4 — Σᵢ‖uᵢ(w)−uᵢ(w′)‖²_* ≤ (n−1)ΣᵢΣ_{j≠i}‖wⱼ−w′ⱼ‖² = (n−1)²Σᵢ‖wᵢ−w′ᵢ‖²
-- statement:
--   Consider an $n$-player game with $d$ strategies per player and utilities $u_i(s) \in [0,1]$, and let $w, w'$ be two mixed profiles (every $w_j, w'_j \in \Delta$). With $u_i(w)$ player $i$'s utility vector against $w_{-i}$,
--   $$\sum_{i} \|u_i(w) - u_i(w')\|_\infty^2 \le (n-1)\sum_i \sum_{j \ne i} \|w_j - w'_j\|_1^2 = (n-1)^2 \sum_i \|w_i - w'_i\|_1^2 .$$
--
--   This is the variation bound of Theorem 4: the total squared movement of the utility vectors is at most $(n-1)^2$ times the total squared movement of the players' strategies. It is what lets the negative terms of the RVU property absorb the positive ones when $\beta (n-1)^2 \le \gamma$.
--
--   **Formalization Note** Stated for two arbitrary mixed profiles; the paper applies it to $w^t$ and $w^{t-1}$. $(n-1)$ is computed in $\mathbb R$.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 4, proof of Theorem 4, display after “so that”

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem theorem_4_variation_bound {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ‖utilVec u w i - utilVec u w' i‖ ^ 2 ≤
      ((n : ℝ) - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i, l1 (w j - w' j) ^ 2 ∧
    ((n : ℝ) - 1) * ∑ i, ∑ j ∈ Finset.univ.erase i, l1 (w j - w' j) ^ 2 =
      ((n : ℝ) - 1) ^ 2 * ∑ i, l1 (w i - w' i) ^ 2 := by sorry

end RegLearnGames.TotalRegret
