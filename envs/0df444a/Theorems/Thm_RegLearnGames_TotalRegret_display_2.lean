-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_display_2
-- name    : RegLearnGames.TotalRegret.display_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:38.118645+00:00
-- url     : https://prove2.me/theorems/92d9aa0c-a463-49d6-b090-c1bb2f4d88c1
-- title:
--   Proof of Theorem 4, display (2), p. 4 — ‖uᵢ(w)−uᵢ(w′)‖_* ≤ TV of the product of the others ≤ Σ_{j≠i}‖wⱼ−w′ⱼ‖₁
-- statement:
--   Consider an $n$-player game with $d$ strategies per player and utilities $u_i(s) \in [0,1]$. Let $w = (w_1,\dots,w_n)$ and $w' = (w'_1,\dots,w'_n)$ be two mixed profiles (every $w_j, w'_j \in \Delta$), and fix a player $i$. Write $u_i(w)$ for player $i$'s utility vector against $w_{-i}$. Then
--   $$\|u_i(w) - u_i(w')\|_\infty \le \sum_{s_{-i}} \Big|\prod_{j\ne i} w_{j,s_j} - \prod_{j \ne i} w'_{j,s_j}\Big| \le \sum_{j\ne i} \|w_j - w'_j\|_1,$$
--   where the middle sum runs over all strategy choices $s_{-i} = (s_j)_{j \ne i}$ of the players other than $i$.
--
--   The middle quantity is (twice) the total variation distance between the two product distributions of the opponents' play; the second inequality is the subadditivity of total variation over product measures. In the paper it is applied with $w = w^t$ and $w' = w^{t-1}$.
--
--   **Formalization Note** The index set $\{j \ne i\}$ is the subtype `{j : Fin n // j ≠ i}`; $\|\cdot\|_\infty$ is Mathlib's sup norm.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 4, proof of Theorem 4, first display and display (2)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem display_2 {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) (i : Fin n) :
    ‖utilVec u w i - utilVec u w' i‖ ≤
        ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| ∧
      ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| ≤
        ∑ j : {j : Fin n // j ≠ i}, l1 (w j.1 - w' j.1) := by sorry

end RegLearnGames.TotalRegret
