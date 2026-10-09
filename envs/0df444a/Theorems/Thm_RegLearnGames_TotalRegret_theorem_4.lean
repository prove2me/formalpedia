-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_theorem_4
-- name    : RegLearnGames.TotalRegret.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:47.680112+00:00
-- url     : https://prove2.me/theorems/b983aab1-6d1f-482f-a577-b3a028ee1b92
-- title:
--   Theorem 4, p. 4 — RVU for every player with β ≤ γ/(n−1)² and ‖·‖ = ‖·‖₁ implies Σᵢ rᵢ(T) ≤ αn
-- statement:
--   Consider an $n$-player game with $d$ strategies per player and utilities $u_i(s) \in [0,1]$, played repeatedly: $w^0, w^1, \dots$ are mixed profiles and $u_i^t = u_i(w^t)$ is player $i$'s utility vector at time $t$ (so $u_i^0$ is computed from $w^0$). Let $\alpha > 0$ and $0 < \beta \le \gamma$ with $\beta(n-1)^2 \le \gamma$, and fix a horizon $T$. Suppose each player's play satisfies the RVU inequality with these constants and $\|\cdot\| = \|\cdot\|_1$: for every player $i$ and every $v \in \Delta$,
--   $$\sum_{t=1}^T\langle v - w_i^t, u_i^t\rangle \le \alpha + \beta\sum_{t=1}^T \|u_i^t - u_i^{t-1}\|_\infty^2 - \gamma \sum_{t=1}^T \|w_i^t - w_i^{t-1}\|_1^2.$$
--   Then for every profile of comparators $(w_i^*)_i$ with each $w_i^* \in \Delta$,
--   $$\sum_{i} \sum_{t=1}^T \langle w_i^* - w_i^t, u_i^t\rangle \le \alpha n,$$
--   that is, $\sum_i r_i(T) \le \alpha n$.
--
--   The sum of all players' regrets is therefore bounded by a constant independent of $T$; with Proposition 2 this makes the average welfare converge to within the price of anarchy of the optimum at rate $O(1/T)$.
--
--   **Formalization Note** The paper's condition $\beta \le \gamma/(n-1)^2$ is written $\beta(n-1)^2 \le \gamma$, which agrees for $n \ge 2$ and avoids division by zero at $n = 1$. The RVU inequality is assumed only on the realized play and for the given horizon, a weaker hypothesis than the paper's "on any sequence of utilities", so the statement is a disclosed strengthening. The bound on $\sum_i r_i(T)$ is stated for every comparator profile, which is equivalent to bounding the sum of suprema.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 4, Theorem 4; Definition 3, inequality (1), p. 3

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem theorem_4 {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : ∀ t i, w t i ∈ stdSimplex ℝ (Fin d))
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hβγn : β * ((n : ℝ) - 1) ^ 2 ≤ γ) (T : ℕ)
    (hRVU : ∀ i, ∀ v ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (v - w t i) ⬝ᵥ utilVec u (w t) i ≤
        α + β * ∑ t ∈ Finset.Icc 1 T, ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2
          - γ * ∑ t ∈ Finset.Icc 1 T, l1 (w t i - w (t - 1) i) ^ 2)
    (wstar : Fin n → Fin d → ℝ) (hwstar : ∀ i, wstar i ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ∑ t ∈ Finset.Icc 1 T, (wstar i - w t i) ⬝ᵥ utilVec u (w t) i ≤ α * n := by sorry

end RegLearnGames.TotalRegret
